# SPEC: repairing the DegreeBound fallback

*Specification for fixing the field-recognition fallback on the g4 branch,
written 2026-11-13, in response to the review of the g4 PR (the 9T6 /
`DegreeBound := 4` reproduction).  Companion to `Doc/adr-genus4.md` §4,
which records the fallback's original design; this spec supersedes that
design.  The fallback exists only on `g4` and `higher-genus`; `master`
still hard-errors, so nothing here is a hotfix.*

## 1. The bug, precisely

`TriangleRecognizeAlgebraicCoefficients`'s fallback tries `K = Q` first,
accepting when the coefficients are real and satisfy degree-1 relations --
but both checks stop after the first 5 nonzero coefficients
(`ntested ge 5`), although the documented intent was every coefficient.
This is not coincidence-prone but systematically wrong: `cfs` lists curve
coefficients before map coefficients, and maps exist whose curve is
defined over `Q` while the map requires a larger field, so the head of
`cfs` is rational by construction exactly in the dangerous case.
Reproduction: the 9T6 example (over `Q(sqrt(-3))`) with
`DegreeBound := 4`; `MakeK` finds no quartic field, the fallback accepts
`Q` on five rational-looking coefficients, and the run dies at the sanity
check instead of succeeding over the quadratic field one retry away.  No
wrong map escapes (the sanity check is the referee, as designed); a
success is converted into a hard error.

## 2. Principles the fix must respect

- **Evidence is asymmetric.**  A coefficient exhibiting an irreducible
  degree-5 minimal polynomial certifies degree >= 5 by itself; no number
  of rational-looking coefficients certifies `K = Q`, because `Q` is the
  bottom of the subfield lattice and every coefficient of every map is
  consistent with it.  Hypotheses low in the lattice are confirmed only
  by totality, never by sampling.
- **The phony floor.**  At degree bound `m` and working precision `prec`,
  LLL returns spurious relations of height about `prec/(m+1)` digits; the
  true padded lower-degree relation (height `h`) surfaces only when
  `h < prec/(m+1)`.  Consequences: degree information is trustworthy only
  from SMALL bounds; per-degree acceptance gates must sit well below that
  degree's floor, not at a flat `prec/4`; and reading the true degree off
  a large-bound relation ("looked like degree 2") is reliable only at
  generous precision, so it is a hint, never a mechanism.
- **The accuracy gradient.**  Coefficients near the leading term carry
  the most correct digits; accuracy decays down the list.  So: CERTIFY
  the field from one good coefficient near the head (minimal polynomial);
  ask the rest only whether they FIT in the candidate field (linear
  algebra over an `O_K` basis, cheaper in digits), with per-coefficient
  gates graded by expected accuracy -- tight at the head, loose at the
  tail.  Demanding correct-degree minimal polynomials of tail
  coefficients converts noise into false rejection of the true field.
- **Reality survives the gradient.**  The imaginary part of a truly real
  coefficient stays at noise level however degraded the expansion, so
  "all coefficients real" is checkable on the whole list, bad tail
  included.  And it is decisive for imaginary fields: an element of an
  imaginary quadratic field that is real is rational, so a map genuinely
  over `Q(sqrt(-3))` has a non-real coefficient somewhere, and the total
  reality check alone rejects `Q` in the 9T6 case.  (For real fields it
  is necessary, not sufficient; the graded degree-1 fits carry the rest.)
- **One trap**: `MakeK(c, 1)` accepts `Q` UNCONDITIONALLY (`m eq 1` is an
  early return).  Degree 1 must never enter a candidate loop bare; the
  total test below is its gate.

## 3. The algorithm (propose / verify)

Numerics are computed once; only recognition repeats.  (The ancestor of
this loop is the descending `try` wrapper in the BelyiDB bulk code, which
re-ran all of `BelyiMap` per degree -- tolerable at genus 0, not above.)

1. **Q first, gated totally.**  Accept `K = Q` only if (a) EVERY
   coefficient in `cfs` is real to working precision, and (b) every
   coefficient passes a degree-1 fit with a gate graded by its position
   (head: well under `10^(prec/2)`'s phony floor, e.g. `10^(prec/4)`;
   tail: loosened by the estimated accuracy loss).  This keeps the fast
   path for the common case (passport members related by the `S_3`
   action: cyclic covers, 9T25, the 11T1 genus-5 tests) at the cost of
   `#cfs` trivial LLLs, and is immune to the 9T6 failure.
2. **Ascend `m = 2, 3, ..., DegreeBound - 1`.**  Propose with the
   EXISTING while-loop over `cfs`: `MakeK(cfs[i], m)` demands an
   irreducible relation of degree exactly `m`, so it already skips
   coefficients lying in proper subfields and finds a primitive one --
   keep it, walking from the head of `cfs` (the accurate end).  Add the
   per-degree height gate `<< 10^(prec/(m+1))` on the proposed relation.
3. **Verify every candidate `K` before accepting it**: recognize all of
   `cfs` over an `O_K` basis with graded gates.  A failure on an
   accurate head coefficient rejects `K` and continues the ascent; a
   failure confined to the noisy tail aborts with the precision error.
   Acceptance without total verification is the bug; this step is not
   optional.
4. **Hints, not shortcuts**: when `MakeK` rejects a proposal whose
   relation factored with a clean lower-degree irreducible factor, vprint
   it and try that degree next; never accept it directly (the phony
   floor).
5. **Error semantics**: exhausting all degrees raises
   "Unable to create number field!", which now genuinely means
   "insufficient precision", the one remedy being `prec`.  The failure
   modes "wrong degree" and "too few digits" are no longer conflated.

Unchanged: `MakeK` itself (except the gate), the sanity check as final
referee, `master`, and the non-fallback path (correct `DegreeBound`),
which was always sound.

## 4. Tests

| test | change |
|---|---|
| `test_degreebound_fallback.m` (new) | the review's reproduction: 9T6 at prec 40 with `DegreeBound := 4`; asserts success, `Degree(K) eq 2`, discriminant `-3`, sanity check |
| `test_genus4_nonhyp_9T6.m` | add `Degree(K) eq 2` and discriminant assertions |
| `test_genus4_nonhyp_9T25.m`, `test_genus4_nonhyp_9T27.m` | add `K eq Rationals()` assertions |
| `test_genus3_*`, `test_genus3_hyp.m` | same field assertions where the field is known |

The field assertions also close most of the review's "tests cannot tell
the passports apart" point: 9T6/9T25/9T27 share ramification `(9,9,9)`
but not fields.  Suite timings must not regress (the Q path gains
`#cfs - 5` tiny LLLs; nothing else is on the fast path).

## 5. Also in this change (review's smaller points)

- **Unify the pivot**: the cubic's centred pivot in `genus4.m`
  re-implements `CentralPivot` from `recognition.m` without the modulus
  tie-break; call the real one.  Do this before `genus-general.m` would
  copy the fork a third time.
- **Comment at `hgate`** recording the margin arithmetic (gate
  `10^(prec/4)` vs observed heights up to 9 at prec 40) and the grading
  rule above.
- **TODO, not now**: held-out columns for the step-6 residual of
  `phi = -A/B` (currently in-sample).

## 6. Out of scope

Compositum construction when no single coefficient is primitive (take
the field of the max-degree coefficient and let verification fail
towards a precision error; no observed case needs more), any change to
genus-0/1 recognition, and the BelyiDB wrapper.

## 7. Implementation notes (2026-11-13, after measurement)

The algorithm of §3 is implemented in `TriangleRecognizeAlgebraicCoefficients`
as written, with four departures forced by measurements made while testing
it on real maps (the genus 2 passports 7T6-[7,7,6] and 7T7-[7,4.3,4.3] from
the LMFDB, whose fields are known).  The numbers are recorded in the gate
comment in `recognition.m`.

1. **Relations are found on an explicit lattice**, rows
   `[e_i | round(10^q Re x_i) | round(10^q Im x_i)]`, not with Magma's
   `PowerRelation` / `LinearRelation`.  Those work at an undocumented
   reduced internal precision (phony relations among two numbers at
   precision p come out at about p/4 digits, not p/2), so the floor of §2
   is not where the spec puts it and the gates cannot be placed relative
   to it.
2. **The lattice scale is q = 4p/5, not p.**  The coefficients carry about
   four fifths of the working precision (41-42 digits of 50 on 7T6-[7,7,6],
   33-34 of 40 on 9T6).  Scaled to p, a genuine relation of height h has a
   lattice vector of length h times the excess and is unrecoverable for
   ordinary h; the 9-digit fits of 7T6-[7,7,6]-b are an example.
3. **Gates sit two digits below the floor, flat in position.**  Half the
   floor rejected three of the four test maps: genuine heights of 9 to 13
   digits at p = 50 are normal.  The accuracy loss is flat across the list,
   not a head-to-tail gradient, so the position grading of §3.1 and §3.3
   has nothing to grade by and is not implemented.  The margin against
   phony is two digits plus their scatter; totality protects Q (every
   coefficient must pass), and verification protects every other field.
4. **A tail failure does not abort.**  A candidate that fits the head and
   fails the tail may be a proper SUBFIELD of the right field: on
   7T7-[7,4.3,4.3]-d a coefficient in the quadratic subfield of the quartic
   field fits 12 coefficients of 19.  That is indistinguishable from a
   precision failure on the right field, so any failure rejects the
   candidate and the ascent continues; when every degree is exhausted the
   error names the best partial fit.  The remedy for both readings is
   `prec`.

5. **The leading coefficient goes through the same fit, and so does every
   coefficient on the non-fallback path** (ungated, with the residual
   check).  The scalar `RecognizeOverK` misrecognized the leading
   coefficient of 7T6-[7,7,6]-b at p = 60 -- its `LinearRelation` was off
   by 3e-24 on 60-digit input while the lattice fit is right to 8e-41 --
   and the sanity check, not the recognition, caught it.  The spec left the
   non-fallback path unchanged on the grounds that it was sound; the field
   it found always was, the coefficients it recognized were not always.

Tests added beyond §4: `test_genus2_fallback_real_quadratic.m`
(7T6-7_7_3.2.2-c over Q(sqrt 7): only the height gate can reject Q) and
`test_genus2_fallback_curve_over_Q.m` (7T7-7_4.3_4.3-c: curve over Q, map
over Q(i), passport 9) and `test_genus2_fallback_large_heights.m`
(7T6-7_7_3.2.2-b over Q(sqrt 21), 12-digit heights, prec 60).  The quartic orbit 7T7-7_4.3_4.3-d is out of reach:
its primitive coefficients have minimal polynomials of 20 or more digits,
beyond any floor at p = 60.

**Follow-up, not in this change (2026-11-14): a centred pivot in genus 2.**
The hyperelliptic path still normalizes by the last entry of each list.
Tried on 7T6-7_7_3.2.2-b: the centred pivot (with the weight lists aligned
to the trimmed coefficient lists, see below) brings the largest fit height
from 2.5e12 down to 4.8e9 and makes the map recognizable at prec 50, where
the last-entry pivot needs 60.  Two things to carry to its own branch:
`TriangleMakeBelyiMap`'s hyperelliptic branch must divide the curve by the
coefficient of y^2 exactly, since a centred pivot no longer makes it 1.
(A second thing the experiment turned up is fixed in this change:
`TriangleHyperellipticNumericalCoefficients` removed trailing zeros from the
numerator and denominator coefficient lists but not from their weight
lists, and the rescaler reads the weights that feed lambda positionally
from `num_vals cat denom_vals`, so a shortened numerator list shifted every
denominator weight it read.  The weight lists are now trimmed with the
coefficient lists.)

**Follow-up, not in this change: verifying the monodromy.**  The sanity
check verifies the ramification data of the passport, not which triple the
map realizes, so 9T25 and 9T27 (both over Q, both of type (9,9,9)) are
indistinguishable to their tests.  A real check would be a separate,
opt-in `VerifyMonodromy`: take a plane model of the curve as a cover of the
phi-line (Gm-Reduce's `BestModel`, https://github.com/SamSchiavone/Gm-Reduce,
was written to produce such models), run Magma's `MonodromyRepresentation`
on it w.r.t. the embedding, and compare the local monodromies at 0, 1, oo
with sigma by simultaneous conjugacy, settling once the two conventions
(which permutation sits over which branch value; orientation, i.e. whether
the triple comes back inverted).  Its cost on the larger examples is
unknown and is the reason it is not on the path of every test.  For
comparison, the certified monodromy computation of
https://arxiv.org/abs/2604.15562 (via the algpath package in Sage) is
reported to have verified the Belyi maps in the LMFDB; it is the standard
to measure a `VerifyMonodromy` against, and an alternative route to one at
the price of a Sage dependency.
