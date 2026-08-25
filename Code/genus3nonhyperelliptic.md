# Belyi maps in genus 3, non-hyperelliptic

Companion notes for `Code/genus3nonhyperelliptic.m` and for the changes it
required in `Code/belyi_main.m`, `Code/recognition.m`, `Code/hackobj.m` and
`Code/spec`.

## What was added

| file | change |
|---|---|
| `Code/genus3nonhyperelliptic.m` | new: `Genus3NonHyperellipticMonomials`, `TriangleGenus3NonHyperellipticTest`, `TriangleGenus3NonHyperellipticNumericalCoefficients` |
| `Code/spec` | lists `genus3nonhyperelliptic.m` |
| `Code/hackobj.m` | attributes `TriangleIsGenus3NonHyperelliptic`, `TriangleGenus3NonHyperellipticDegree` |
| `Code/belyi_main.m` | genus 3 non-hyperelliptic branch replaces the `error` at the end of the genus `>= 2` dispatch |
| `Code/recognition.m` | `TriangleRecognizeAlgebraicCoefficients` and `TriangleMakeBelyiMap` widened; `TriangleRescaleCoefficients` gains a working `rescale_ind`, is documented, its `print`s become `vprint`, its weight-zero error names the group |
| `Tests/test_genus3nonhyperelliptic_belyi.m` | KMSV Example 5.27, degree 7 |
| `Tests/test_genus3nonhyperelliptic_degree8.m` | degree 8, cyclic: `dim I_d != 0`, and a triple with `sigma_0` in two cycles (RUNSLOW) |
| `Tests/test_genus3nonhyperelliptic_generic.m` | degree 8, full `S_8`, trivial `Aut(phi)` (RUNSLOW, exploratory) |
| `Tests/run_tests.sh` | runs all three |

Naming follows the dispatch rather than the model: the cases in
`belyi_main.m` are distinguished by genus and by hyperellipticity, and
"genus 3, non-hyperelliptic" is what this branch *is*.  That the canonical
model of such a curve is a smooth plane quartic is a consequence.

## The construction

Full detail is in the header comment of the source.  In brief:

- The canonical class is the hyperplane class `H`; affine coordinates
  `x = f_1/f_3`, `y = f_2/f_3` on the patch `f_3 != 0`.
- `A + phi*B = 0` as **series at P** is the same as `A + phi*B = 0` as
  functions, so the pairs of degree-`d` forms correspond to
  `B in H^0(dH - phi^*(oo))` with `A = -phi*B`.  Nothing in this needs to see
  where `phi` vanishes or has poles away from `P`, so **`sigma_0` may have any
  number of cycles**.
- That space has dimension `4d - N - 2 >= 3`, and every element gives the same
  `phi` with wildly different heights.  Additionally requiring
  `ord_P(B) >= j` cuts it to `H^0(dH - phi^*(oo) - j*P)`, which lets `j` tune
  the dimension one step at a time; the code walks `j` until the dimension is
  exactly **1**, so there is no representative to choose.  This is
  `hyperelliptic.m`'s `while ... t := t - 1` idea in the coordinates available
  here.
- Both halves are reduced modulo `I_d` **before** echelonizing.  Not optional.
- The residual of the joint relation is reported and gated: it is the
  statement that `phi = -A/B` on this curve, to full precision.

### Why not a `RiemannRochBasisGenus3NonHyperellipticAnalytic`

The natural reading of MSSV section 6.3 is `phi_0 in L(t*P)`,
`phi_inf = phi_0/phi in L((s+t)*P)`, which is what `hyperelliptic.m`
implements.  That function can exist there because the hyperelliptic model
hands it `x` and `y`, global functions whose pole divisors are known a priori
to sit at infinity: `L(m*infinity)` is then the monomials in them of low
enough pole order, plus a `PolarPart` subtraction to kill the second point at
infinity.

A plane quartic has no such coordinates at a general `P`.  "Poles only at `P`"
is a condition about the other three points where a line through `P` meets the
curve, and a single power series at `P` carries no information about them --
so `L(m*P)` cannot be assembled from the data this stage has.  It *is*
obtainable from the plane model: `P = (1:0:0)` exactly (the basis is
echelonized, so `f_1(P) != 0` and `f_2, f_3` vanish), the residual of any line
through `P` is a root-finding problem on the numerical quartic, and vanishing
on that residual is a linear condition.  That was not done: it introduces
numerical root-finding, multiplicity detection and near-degenerate vanishing
conditions -- a new and untestable source of fragility -- to buy three things
the vanishing-order tuning already buys out of machinery that is here.

**If a later revision does want `L(m*P)`, the blocker is exactly that
root-finding step, not the linear algebra around it.**

## What is verified, and what is not

The mathematics comes from a verified reference implementation
(`kmsv_genus3.m` in `M23-recompute`) plus the genus-4 corrections.  The
packaging into intrinsics was written **without access to Magma** and has not
been executed.  Claims to check first, roughly in order of how likely they are
to bite.

### Claims about control flow

1. **`TriangleHyperellipticTest` returns `false` rather than erroring on a
   non-hyperelliptic genus 3 curve.**  `belyi_main.m` runs the hyperelliptic
   test first and only reaches the new branch when it returns `false`; but
   that intrinsic errors with `"Multiple hyperelliptic relations found!"` when
   its kernel has dimension `> 1`.  Its 15 test functions are `x^i`, `x^i y`,
   `y^2` for `x = f_1/f_2` and `y = x'/f_3`, which is not the coordinate
   system used here, and whether they are independent on a smooth plane
   quartic was not checked.  If that error fires, the new branch is never
   reached.
2. **The `assigned` guards do not change genus 1 or genus 2 behaviour.**
   Magma's `or` short circuits, so genus 2 never touches either attribute.
   `Tests/run_tests.sh` is the check.
3. **`rescale_ind` defaults to the previous behaviour.**  `rescale_ind := 0`
   normalizes each list by its FINAL entry, exactly as before, so
   `hyperelliptic.m` and the genus 1 path are unchanged; only the new caller
   passes indices.  `test_basic_belyi.m` is the check.

### Claims about the numerics

4. **`ord_w(phi) = a`, the first entry of `DefiningABC`, and `ord_P(phi) = s`,
   the length of the cycle of `sigma_0` containing the base point.**
   `TrianglePhi` reverts `psip ~ t^(1/a)`, so `phi ~ w^a`.  The stride
   `e = a div s` is then the order of the stabilizer at `P`, the same `e`
   `hyperelliptic.m` computes, and every ratio of forms has `w`-exponents
   divisible by it.  All column counts are in strided units, and the code
   errors immediately if `Valuation(phipser) ne a` or if `e*s ne a`.
5. **The dimension walk terminates.**  `dim H^0(dH - D_inf - j*P)` is
   non-increasing in `j`, drops by at most 1 per step (one linear condition),
   and is `4d - N - 2 >= 3` at `j = 0`, so some `j` gives exactly 1 and a
   monotone walk reaches it without oscillating.  The walk starts at
   `j = 4d - N - 3`, which is the answer whenever the divisor is nonspecial --
   it has degree 3, below `2g - 1 = 5`, so specialty is possible, which is
   what the loop is for.  Numerically the computed dimension could still jump,
   so the loop has an iteration cap.
6. **`NumericalKernel` is used only where `ncols >= nrows`.**  The vanishing
   conditions are the one place with fewer conditions than unknowns, and there
   `G3NonHypConditionNullSpace` does an RREF of the condition matrix instead.
7. **`Genus3NonHyperellipticMonomials`' ordering is no longer load-bearing.**
   With `rescale_ind` the rescaler no longer needs the final entry to be
   nonzero.  What is still needed is that the weight-zero monomial `[0,0]` is
   PRESENT with a nonzero coefficient somewhere in numerator or denominator,
   since that is the coefficient `lambda`'s Bezout patch reads.  If both `A`
   and `B` have zero constant term, `TriangleRescaleCoefficients` still errors
   -- and that is a genuine limitation of its algorithm, not of the ordering.
8. **The `s_i` are increasing, so `[0,0]` is the unique affine weight-zero
   monomial.**  Enforced by `require ord(f_1/f_3) < 0 and ord(f_2/f_3) < 0`.
9. **`lambda^(1/gcd)` when `gcd > 1`.**  All affine weights are divisible by
   the stride `e`, so whenever `e > 1` the rescaler's `gcd` is too and its
   root of `lambda` is determined only up to a root of unity.  Pre-existing
   behaviour shared with the hyperelliptic path, now warned about via
   `vprint`.  Dividing the valuations by `e` first would remove the ambiguity
   -- `lambda` becomes `mu^(-e)` and `lambda^(v/e)` is the same rescaling --
   but that departs from what `hyperelliptic.m` passes, so it was not done.

### Claims about Magma itself

10. **`import "genuszero.m" : RemoveLeadingZeros;`** -- the same import
    `triangle_phi.m` and `values.m` already do.
11. **`Parent(serd[1])!phipser`** coerces the rational power series for `phi`
    into the complex series ring.  `hyperelliptic.m` relies on the same
    coercion implicitly in `f*phi`.
12. **`AbsolutePrecision` of the constant monomial.**  `x^0 y^0` is the exact
    `1`, whose absolute precision is infinite and not an integer;
    `G3NonHypColumnsAvailable` skips any such element rather than comparing
    it.
13. **`FunctionField(Curve(ProjectiveSpace(K, 2), Q)).1` and `.2` are the
    affine coordinates on the patch where the LAST variable is 1**, so they
    are `x = f_1/f_3` and `y = f_2/f_3`.  If this is wrong the curve is still
    right but `phi` is evaluated in the wrong chart and
    `BelyiMapSanityCheck` fails.

### Claims about the tests

14. **`DegreeBound` is passed explicitly where the field is known** -- 2 for
    KMSV 5.27 (`K = Q(sqrt(-7))`, and the triple is rigid so the default
    passport size may be 1, which makes `MakeK` short circuit to `K = Q`), and
    1 for the two cyclic degree-8 triples (defined over `Q`; the default would
    send `MakeK` hunting for a field that does not exist).  Neither passport
    size was computed.  `test_genus3nonhyperelliptic_generic.m` leaves the
    default, because nothing is known about its field.
15. **The degree-8 cyclic pair is derived, not looked up.**  The curve is
    `y^8 = x(x-1)^5`; its canonical coordinates carry distinct `C_8` weights
    `3, 6, 7`, no invariant quadric exists, so the curve is **not**
    hyperelliptic -- and the same computation for `y^8 = x(x-1)` produces the
    quadric `w_5 w_7 - w_6^2`, correctly identifying that control as
    hyperelliptic.  The second triple in that file is the first with `0` and
    `oo` swapped: the SAME curve, but with `sigma_0` in two cycles.  If the
    first passes and the second fails, the multi-cycle handling is what broke
    and nothing else.
16. **`test_genus3nonhyperelliptic_generic.m` is exploratory.**  Its field of
    definition, passport size, and even its non-hyperellipticity are unknown;
    `prec` and the default `DegreeBound` are guesses.  Read its header before
    treating a failure there as a regression.
17. **No runtime was measured.**  The KMSV case is ungated; if it dominates
    the suite, move its `run_magma_test` line under the `RUNSLOW` guard rather
    than lowering `prec` to where recognition becomes marginal.  All three use
    the external C solver when `POWSER_ARNOLDI_BIN` is available.

## Gates that are NOT implemented

Of the three gates for deciding whether a run worked, only the second is here.

- **Residual against the lattice's reach.**  A degree-`n`, height-`h` fit is
  meaningful only if its residual beats `10^(-h(n+1)/2)` by a margin; a fit
  sitting *at* the reach is LLL saturating, not a value.  That belongs in
  `MakeK` / `RecognizeOverK` (`theta.m`) and was left alone.  Stability across
  precisions is **not** a substitute: a spurious fit is reproducible.
- **Exact ramification.**  This is `BelyiMapSanityCheck`, which runs, plus the
  per-fibre cycle-type assertions in the degree-8 tests.  Note that a place of
  residue degree `f` with valuation `m` contributes `m` repeated `f` **times**;
  using `m*f` once turns `2^8 1^7` into `[1,2,2,2,4,4,8]` -- the right total
  with the wrong partition -- and fails a correct map.
- **Height, measured rather than inferred.**  If recognition fails, neither
  "bug" nor "precision" is a conclusion: compute the map exactly at many split
  primes and CRT, and the prime count at which each coefficient stabilizes
  *is* its height.  A diagnostic, not test-suite code.

One reading recorded so it is not repeated: "precision failure is graded, so
all-or-nothing failure means a bug" is only valid when the true heights are
spread.  Clustered heights straddling the certification limit fail together
with no bug present.

## Deliberately out of scope

- Genus 3 hyperelliptic: already handled by the existing path.
- Genus `>= 4`: needs a quadric-and-cubic model in `P^3`.
- `L(m*P)` as an explicit basis of series, and with it the literal MSSV
  `L(t*P)` / `L((s+t)*P)` formulation.  See above for what the blocker is.
- Newton refinement (`newton_hyperelliptic.m`) for plane quartics.
- `BelyiDB` integration: storing plane-quartic models needs a decision about
  `plane_model` versus `curve` in the database schema.
