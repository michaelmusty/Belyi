# Tests

Run everything (from the repository root):

```
sh Tests/run_tests.sh          # quick tests (~a few minutes)
RUNSLOW=1 sh Tests/run_tests.sh   # also runs the slow consistency test
```

The runner executes, in order:

1. **C solver selftest** (`Cext/powser_arnoldi --selftest`): synthetic dense
   eigenproblem + high-precision SVD kernel detection, checked by residuals.
   Skipped if the binary is absent and cannot be built.
2. **`test_basic_belyi.m`**: the README example (degree 4, genus 0) through
   the classical pipeline, verified exactly via `BelyiMapSanityCheck`.
3. **`test_carnoldi_belyi.m`**: the same example through the external C
   solver (`PowserAl := "CArnoldi"`), verified exactly.  Skipped if the
   solver binary is not found (set `POWSER_ARNOLDI_BIN`).
4. **`test_genusone_extra_zero.m`**: three genus-1 maps through the Newton
   lift, verified exactly, covering all branches of the extra-common-zero
   predicate `NeedsExtra` (the extra zero is present iff the 0-fiber does
   NOT sum to O in the group law).  4T5-4_4_3.1-a has `sigma_0` a d-cycle
   (0 totally ramified): no extra zero, `NeedsExtra` false.
   6T12-5.1_5.1_3.3-a has `sigma_0` of type 5.1, where the special point
   P_s = -(sum of the 0-fiber) is provably nonzero: `NeedsExtra` true, and
   Newton must track the special point (2 extra variables, 3 extra
   equations) for the system to be square.  6T7-4.2_4.2_3.3-a is the
   degenerate case: `sigma_0` of type 4.2 (s < d) but the map factors
   through the x-line, so the 0-fiber is 4*O + 2*(2-torsion) and sums to O:
   no extra zero despite s < d, `NeedsExtra` false — which shows the
   predicate must be data-driven, not combinatorial.
5. **`test_powser_consistency.m`** (slow, `RUNSLOW=1`): degree-7 example;
   computes the weight-4 power series basis with both `Al := "Arnoldi"` and
   `Al := "CArnoldi"` at 100 digits and asserts the echelonized bases agree
   as functions to 1e-70, that both minimal singular values are below
   eps_thresh, and that the echelon pivot structure is exact.

Each Magma test prints `ALL TESTS PASSED` on success or `SKIP: ...` when a
prerequisite (the C binary) is missing; the runner treats anything else as
failure and shows the tail of the output.

Notes for test authors: attach the spec with `AttachSpec("Code/spec");`
(tests run from the repo root), end scripts with `quit;`, and remember that
`PowerSeriesBasis` caches results on `Gamma` keyed by its parameters
(including `Al`) — use fresh `TriangleSubgroup` objects when you need
independent runs.
