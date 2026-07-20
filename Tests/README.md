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
4. **`test_powser_consistency.m`** (slow, `RUNSLOW=1`): degree-7 example;
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
