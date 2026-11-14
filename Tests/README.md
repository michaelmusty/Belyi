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
5. **`test_genusone_aj.m`**: unit tests for the genus-1 Abel-Jacobi
   evaluation.  On two examples (4T5-4_4_3.1-a, and a (5,5,4) triple whose
   chart layout is kept as a regression), checks that the exact coset-path
   evaluation (`TriangleCosetVertexToComplexPlane`) and the adaptive path
   integrator (`TriangleDiscToComplexPlane`) agree modulo the period
   lattice at every fundamental domain vertex, and that all ramification
   points satisfy the curve equation to working accuracy (the original
   single-expansion evaluation left only ~5 correct digits).
6. **`test_powser_consistency.m`** (slow, `RUNSLOW=1`): degree-7 example;
   computes the weight-4 power series basis with both `Al := "Arnoldi"` and
   `Al := "CArnoldi"` at 100 digits and asserts the echelonized bases agree
   as functions to 1e-70, that both minimal singular values are below
   eps_thresh, and that the echelon pivot structure is exact.

7. **`test_genus4_hyp_9T1.m`**: genus 4 but HYPERELLIPTIC (the cyclic
   cover 9T1-[9,9,9]): checks that the dispatch routes it to the existing
   hyperelliptic path and not to the quadric-and-cubic branch, and verifies
   the closed form `y^2 = x^10 - 2x`, `phi = (y + x^5)/(2x^5)` independently.
   `DegreeBound := 1` is passed: the passport's three members are related by
   permuting `0, 1, oo`, not by Galois, so each is over `Q`.
8. **`test_genus4_nonhyp_9T25.m`**, **`test_genus4_nonhyp_9T6.m`**, and
   (slow, `RUNSLOW=1`) **`test_genus4_nonhyp_9T27.m`**: genus 4, not hyperelliptic, the
   canonical model a quadric meeting a cubic in `P^3` (`Code/genus4.m`), on
   the degree-9 `(9,9,9)` passports from BelyiDB.  9T25 (over `Q`, trivial
   `Aut`, passport size 4) passes no `DegreeBound` and so exercises the
   fallback in `TriangleRecognizeAlgebraicCoefficients` from the passport
   size down to `Q`; 9T6 (over `Q(sqrt(-3))`, `Aut` of order 3) exercises the
   weight-gcd branch of the rescaler; 9T27 (over `Q`, passport size 6) needs
   `prec := 80` (at 60 the recognition over `Q` accepts a wrong `B` and the
   sanity check catches it) and takes about six minutes on its own, which is
   why it is gated.  Assertions are on the ramification and on the field of
   definition (`Q` for 9T25 and 9T27, `Q(sqrt(-3))` for 9T6), which is what
   tells the three `(9,9,9)` passports apart.
9. **`test_degreebound_fallback.m`**: the `DegreeBound` fallback of
   `TriangleRecognizeAlgebraicCoefficients` (`Doc/SPEC-degreebound-fallback.md`):
   9T6 with `DegreeBound := 4`, forced above the field degree.  `MakeK` finds
   no quartic field; the fallback must reject `Q` (the curve's coefficients
   are rational but the map's are not all real) and find `Q(sqrt(-3))`,
   verified on every coefficient.  Asserts the field's degree and
   discriminant and the sanity check.
10. **`test_genus2_fallback_real_quadratic.m`**, **`test_genus2_fallback_curve_over_Q.m`**:
   the same fallback on genus 2 maps from the LMFDB whose passports split
   into several Galois orbits.  7T6-7_7_3.2.2-c is over the REAL field
   `Q(sqrt 7)`, so reality cannot reject `Q` and only the height gate on the
   degree-1 fits can; 7T7-7_4.3_4.3-c has its curve over `Q` and its map over
   `Q(i)`, the exact shape that fooled the old five-coefficient sample.
   **`test_genus2_fallback_large_heights.m`** is 7T6-7_7_3.2.2-b over
   `Q(sqrt 21)`, whose coefficients reach 12 digits of height and whose
   leading coefficient the old scalar recognition got wrong at `prec := 60`.
   Triples are as the LMFDB gives them (shared convention
   `sigma[3]*sigma[2]*sigma[1] = 1`).
Each Magma test prints `ALL TESTS PASSED` on success or `SKIP: ...` when a
prerequisite (the C binary) is missing; the runner treats anything else as
failure and shows the tail of the output.

Notes for test authors: attach the spec with `AttachSpec("Code/spec");`
(tests run from the repo root), end scripts with `quit;`, and remember that
`PowerSeriesBasis` caches results on `Gamma` keyed by its parameters
(including `Al`) — use fresh `TriangleSubgroup` objects when you need
independent runs.
