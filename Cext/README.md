# Cext — external C solver for `PowerSeriesBasis`

`powser_arnoldi.c` reimplements the Arnoldi / numerical-kernel stage of
`Code/powser_iter_arfed.m` in C using FLINT 3 (`acb` arbitrary-precision
complex arithmetic).  Profiling (degree 7 example, prec 100) shows ~95% of
`PowerSeriesBasis` time is the Arnoldi matrix-vector product; this solver
exploits structure that the dense matvec cannot:

* **Wp side** — the "Vandermonde" matrix product is polynomial evaluation
  at the FD-reduced points: Horner's rule, parallelized across points
  with pthreads.
* **J side** — the circle points are exactly `rho * (Q-th roots of unity)`,
  so this matvec is a pointwise weight followed by a **length-Q DFT**
  (`acb_dft`, O(Q log Q) instead of O(N·Q)).
* The numerical kernel of `H - 1` is computed by a high-precision one-sided
  Jacobi SVD on the small Hessenberg matrix, mirroring the escape logic of
  the Magma code.
* Every returned vector `x` is validated: the solver computes the residual
  `|Ax - x|/|x|` from the midpoints of the final ball matvec (the honest
  size, typically ~10^-(prec - few digits); the Magma glue requires it
  below 10^-(epsdigs - 4)), and separately prints a certified ball
  upper bound -- which is dominated by the interval radii of the O(N·Q)
  matvec and is therefore much larger (~1e-54 at prec 100); do not mistake
  the certified bound for the residual itself.

Observed on a 2-core cloud sandbox at the degree-7 / prec-100 example size:
~0.16 s per Arnoldi iteration vs ~2.3 s in Magma (single Apple/Intel core),
before any gain from additional cores.

## Build

Linux: `make` (needs `libflint-dev` >= 3.0, `libmpfr-dev`, `libgmp-dev`).
macOS: `brew install flint mpfr gmp`, then `make mac`.
Sanity check: `make test` (runs a synthetic dense eigenproblem + SVD test).

## Use from Magma

```
AttachSpec("Code/spec");
// once per shell, or put the binary on PATH:
// export POWSER_ARNOLDI_BIN=/path/to/Belyi/Cext/powser_arnoldi
// export POWSER_ARNOLDI_THREADS=8   (defaults to 4)
Sk := PowerSeriesBasis(Gamma, k : dim := 2, Al := "CArnoldi");
```

The Magma glue (the `Al eq "CArnoldi"` branch in `powser_iter_arfed.m`)
writes the problem data to `/tmp/powser_in_<pid>.txt`, invokes the binary,
and reads back `/tmp/powser_out_<pid>.m`.  The geometry (fundamental-domain
reduction, `Js`/`Wps` setup) and post-processing (fill/split, normalize,
echelonize) are unchanged Magma code, and the original `Al := "Arnoldi"`
path is untouched — use it as the correctness oracle:

```
Sk1 := PowerSeriesBasis(Gamma, k : dim := 2, Al := "Arnoldi");
// rebuild Gamma (results are cached on Gamma by input parameters!)
Sk2 := PowerSeriesBasis(Gamma2, k : dim := 2, Al := "CArnoldi");
// compare Sk1[1] vs Sk2[1] coefficientwise
```

Small differences (well below eps_thresh) are expected: the C solver uses
Hermitian inner products in Gram-Schmidt where Magma's `InnerProduct` on
complex vector spaces is bilinear, so the Krylov bases differ; after
echelonization the basis should agree to working precision.

## Numerical notes

* The Arnoldi recurrence runs on midpoints (floating-point at `prec` bits,
  like Magma), not ball arithmetic: near breakdown, ball radii blow up and
  poison the Hessenberg with NaNs.  Rigor comes from the final residual
  check, not from interval propagation.
* On Arnoldi breakdown (exact invariant subspace) or maxiter without a
  formal escape, the solver falls back to the best kernel vector seen if
  its singular value is below eps_thresh.
* Exit status: 0 = all `dim` vectors converged; 2 = some did not (the Magma
  glue raises an error in that case).
