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
