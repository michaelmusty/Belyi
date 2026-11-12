# Review of `SPEC-genus5plus.md`

*Written 2026-11-11, against the `higher-genus` branch after its rebase
onto `g4` (spec commit on top of the five genus-4 commits).  Read
`Doc/SPEC-genus5plus.md` first; section numbers below refer to it.*

## 0. Base branch

The spec treats genus 4 as merged.  Before the rebase `higher-genus` sat on
`master`, which has no `genus4.m`, no `Doc/genus4.md`, no
`Doc/adr-genus4.md`, no `"Centred"` pivot, no `DegreeBound` fallback and a
refusal at genus > 3.  After the rebase every file the spec cites exists
and §2, §5 and §6 are implementable as written.  One stale pointer
remains: §0 says this spec succeeds `SPEC-genus4.md`, which lives in
`M23-recompute`, not in `Doc`.

## 1. Concerns

1. **No `TriangleRescaleCoefficients` audit is needed (§2, §5).**  The
   plan in §5 is right: hand the rescaler the first RREF quadric alone as
   the curve, then rescale every other quadric and cubic by the same
   `lambda` and normalize each by its own centred pivot.  That is what
   `TriangleGenus4NumericalCoefficients` already does with its quadric and
   cubic (`Code/genus4.m`, step 7, "the cubic, by hand"), and it extends to
   `dim I_2 + (g - 3)` forms with a loop in the caller.  The rescaler
   itself only ever sees one curve group, so the sentence in §2 and §5
   saying it "must be audited for more than two form groups" sends the
   implementer into `recognition.m` for nothing; drop it.

2. **Withdrawn.**  §4 builds the `I_d` reduction basis from the stored
   generators and makes its dimension a hard cross-check of the Petri
   class, where `genus4.m` reads `I_d` off numerically.  Sam confirmed
   this is deliberate: which generators are computed depends on the Petri
   classification, so the classification is meant to be load-bearing.

3. **Folded into the spec as §3a, with tests in §7.**  The hyperelliptic
   test is genus-agnostic in form, with a hard-coded column hack.  `TriangleHyperellipticTest` (`Code/hyperelliptic.m`,
   the `M := Matrix(...)` line) builds `3g + 6` series and a matrix of
   `3g + 21` columns, with the comment "just for one example".  The test
   is sound in any genus (a relation among `x^i`, `x^i y`, `y^2` forces
   `[C(X) : C(x)] = 2`), but the fixed 15 spare columns and
   `eps = 10^(-prec/2)` have never run above genus 4.  The §7
   hyperelliptic test is the right check; the spec should name this line
   as what it is testing.

4. **Acknowledged; to be measured, not pre-empted.**  Power-series
   length, not `prec`, is the likely wall.  For the
   degree-11 genus-5 tests `d = 3`: 35 cubic monomials, a joint system of
   70 rows, and the `genus4.m` conventions want up to `6 * 35 = 210`
   strided columns.  A degree-13 fallback (§8) at `d = 4` has 70
   monomials and 140 rows.  The binding constraint is how many series
   terms `PowerSeriesBasis` returns at a given `prec`, which the genus-4
   work never measured against ideal size.  "Precision and patience"
   (§6) understates this.

5. **Resolved in §7.**  Sam recomputed the passport with `Weak := true`:
   size 2, the two curves exactly.  The spec now prescribes
   `DegreeBound := 2` (or 1) for the 11T1 tests, with the caveat that the
   weak size bounds the lax field of moduli only.  Original note: the
   11T1 tests should pass `DegreeBound := 1`.  Passport size is 9
   and the members are related by the `S_3` action, not Galois.  The
   fallback tries `Q` first with a height gate of `10^(prec/4)`, then
   every smaller degree; every existing cyclic-over-`Q` test
   (`test_genus3_nonhyp_deg8.m`, `test_genus4_hyp_9T1.m`, both 9T27
   tests) passes `DegreeBound := 1` for this reason.  §7 should prescribe
   the same for both 11T1 tests, and §5's "exercised hard" should be
   reserved for one test chosen on purpose.

6. **Folded into §9 of the spec.**  The weight-gcd branch: harmless when
   genuine, a sparsity accident otherwise.  The rescaler reads `lambda` from the map's coefficients
   and takes a `gcd`-th root, determined up to a root of unity `zeta`.
   - When the gcd reflects an automorphism of order `d` fixing `P`, the
     canonical ideal is invariant under the torus element `zeta`, and by
     uniqueness of the RREF every row's offsets `w_m - w_piv` are
     divisible by `d`.  The root never matters.  This is why 9T6 was
     clean and is the generic case, including `Aut = C11` on the 11T1
     tests.
   - The accident (Sam's phrasing): the tuned `A`, `B` can be sparse
     enough that their weights share a factor by chance, with no
     automorphism behind it.  The wrong root then multiplies curve
     coefficients by `zeta^(w_m - w_piv)` and leaves the map alone.  That
     is the SAME Belyi map in coordinates over `K(zeta_d)`, so the sanity
     check passes; recognition at the degree bound fails, the fallback
     only walks downward, and the run ends in a hard error.  The
     rescaler's comment that the branch is "resolved downstream by
     BelyiMapSanityCheck" names the wrong mechanism.
   - Cheap fix, should it ever bite: include each curve row's ratios
     `c_m / c_piv`, of weight `w_m - w_piv` and free of any group scalar,
     in the `Xgcd` alongside the map's coefficients.  A common divisor of
     the whole data is then a genuine automorphism.  Applied to the map's
     own ratios the same trick would remove the weight-zero-coefficient
     requirement of §9, but that is a larger change.

7. **Smaller inconsistencies.**
   - (Fixed in §3 and §6.)  `TrianglePetriTest` now takes `(Sk, Gamma)`
     like every sibling test.
   - (Fixed in §8.)  The spec said the two 11T5 members have
     `sigma_0 = s^2` and `s^(-2)`; which slot carries the power depends
     on representative choice, and §8 now says so.
   - (Accepted; §9 hedge widened.)  `IsNonsingular` and the `Curve`
     constructor's dimension check may be slow alongside `Genus` for
     non-complete-intersection models from `g = 6`; §9 now names all of
     them in the `RUNSLOW` downgrade.

## 2. Verified

- Passport sizes (§7, §8).  `PassportRepresentatives(11 : genus := 5)`
  finishes in 25 s, so the Stage-0 input is cheap.

  | group | passports of genus 5 | size |
  |---|---|---|
  | 11T1 | 1 | 9 |
  | 11T5 | 1 | 2 |
  | 11T6 | 1 | 30 |
  | 11T7 | 1 | 54949 |
  | 11T8 | 0 | |

- Closed forms (§7), in Magma over `Q`: `y^11 = x(1 - x)` has genus 5 and
  is hyperelliptic.  `y^11 = x(1 - x)^2` has genus 5, is not
  hyperelliptic, `y` has degree 3, and the canonical ideal in `P^4` has
  minimal generators of degrees `{2, 2, 2, 3, 3}` -- three quadrics and
  two cubics, as the trigonal test asserts.
- The counting table in §1 (monomial counts, `dim I_2`, `dim I_3`, general
  and exceptional ranks for `g = 5, 6, 7`), and the claim that the quartic
  scroll and the Veronese surface share a Hilbert function.

## 3. Open

The Petri class of the 11T5 curve (§8, Stage 0) is still unknown.  It
needs only `PowerSeriesBasis` at 30 digits plus two numerical kernels.
§8 now fixes the order of work: write `petri.m` first and use it as the
Stage-0 computation, with the hyperelliptic test run ahead of it and the
column counts printed, before `genus-general.m` is started.
