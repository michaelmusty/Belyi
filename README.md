# Belyi

After cloning, include dependencies:
```
git submodule init
git submodule update --recursive --remote
```
This allows significant performance improvements using Pari/GP (using `polredabs`); the code will still run if you do not have Pari/GP installed.

After that, run magma in this directory attaching the spec: 
```
AttachSpec("Code/spec");
```

The following gives a basic test:
```
sigma := [Sym(4) | (1,2,3,4), (1,3,4,2), (1,3,4)];
// SetVerbose("Shimura", true);   (uncomment for verbose output)
X, phi := BelyiMap(sigma);
```

## Fast C solver for the power series basis

The dominant cost of `BelyiMap` is computing the numerical power series
basis (`PowerSeriesBasis`, Hejhal's method).  `Cext/` contains an external
C solver that performs this stage 10-20x faster by exploiting the structure
of the linear algebra (the circle points are exactly `rho` times the Q-th
roots of unity, so half the matrix-vector product is an FFT; the other half
is threaded polynomial evaluation) and by running multithreaded, which
Magma cannot.  The output is validated: the solver certifies each computed
basis vector by its residual, and the test suite checks that both pipelines
produce identical exact Belyi maps.

### Building

Requires [FLINT](https://flintlib.org) >= 3.0 (with MPFR and GMP).

Linux (with `libflint-dev` installed):
```
cd Cext && make
```

macOS (with `brew install flint mpfr gmp`):
```
cd Cext && make mac
```

On a server without admin rights, build the dependencies into your home
directory first (10-30 minutes, no root needed):
```
cd Cext && sh build_deps.sh && make server
```

Then check the build:
```
./powser_arnoldi --selftest    # should end with SELFTEST PASSED
```

### Using it from Magma

Export two environment variables in the shell that launches Magma (the
solver is invoked via `System`, which inherits the environment):
```
export POWSER_ARNOLDI_BIN=/path/to/Belyi/Cext/powser_arnoldi
export POWSER_ARNOLDI_THREADS=8      # threads for the solver; 8-16 is a
                                     # good choice, more rarely helps
```

Then pass `PowserAl := "CArnoldi"` to `BelyiMap`:
```
sigma := [Sym(4) | (1,2,3,4), (1,3,4,2), (1,3,4)];
X, phi := BelyiMap(sigma : PowserAl := "CArnoldi");
```
or call the basis computation directly with `Al := "CArnoldi"`:
```
Sk := PowerSeriesBasis(Gamma, k : dim := 2, Al := "CArnoldi");
```

The classical pure-Magma path remains the default (`PowserAl := "Arnoldi"`)
and is unchanged.  Timing reference: the degree-7 example of
Klug-Musty-Schiavone-Voight (Example 5.15, precision 100) runs end-to-end
in ~23 s with the C solver versus ~170 s without, on a 16-core machine.

Implementation notes, the input/output file formats, and numerical details
are documented in `Cext/README.md`.

## Fast certified recognition for MakeK (number field of the Belyi map)

After the numerical solve, `BelyiMap` must recognize the coefficient field
K from complex approximations (`MakeK` in `Code/theta.m`).  The legacy
search calls Magma's `PowerRelation` once per (coefficient, degree) pair —
up to `passport size x #coefficients` sequential LLL calls, each of which
can take minutes at high precision — and when the working precision is too
low to certify any relation it grinds through the entire loop before
failing (observed: 15+ CPU-hours of doomed `MakeK` calls on an M24 genus-0
run at `prec := 400`).

`Cext/makek_relfinder` replaces the loop with one batched, threaded pass:
a single `fmpz_lll` integer-relation reduction per coefficient at the
passport degree bound, followed by `fmpz_poly_factor` and an arb-certified
check of which irreducible factor actually vanishes at the coefficient.
The true minimal polynomial of any degree up to the bound falls out
directly; if nothing certifies, the run aborts within seconds with an
explicit "raise prec" error instead of days of grinding.

Build it with the same `make` as above, then:
```
export MAKEK_RELFINDER_BIN=/path/to/Belyi/Cext/makek_relfinder
export MAKEK_RELFINDER_THREADS=8
```
The batched path is used by the genus-0 recognition stage whenever
`MAKEK_RELFINDER_BIN` is set; unset it to fall back to the legacy search,
which is unchanged and remains the default.

## Tests

```
sh Tests/run_tests.sh              # quick tests
RUNSLOW=1 sh Tests/run_tests.sh    # includes the slow consistency test
```
See `Tests/README.md` for details.

