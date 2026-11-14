# ADR: Belyi maps in genus 4, non-hyperelliptic

*Decision record for `Code/genus4.m`.  The construction itself is
documented in `Doc/genus4.md`; this file records what was decided, what
else was considered, and what measurement settled it.  The work was
specified in `M23-recompute/SPEC-genus4.md` (2026-08-25) after the
degree-9 genus-4 computations there, and implemented on the g4 branch,
2026-11-11.*

## 1. Canonical model and coordinates

**Decision.** A non-hyperelliptic genus-4 curve is the intersection of its
unique canonical quadric `Q` and a cubic `C` in `P^3`.  Work in affine
coordinates `x = f_1/f_4`, `y = f_2/f_4`, `z = f_3/f_4` on the patch
`f_4 != 0`, exactly as genus 3 works on `f_3 != 0`.  `phi = -A/B` with
`A`, `B` of the least degree `d` with `6d - N > 6` (`d = 3` for `N = 9`,
`d = 5` for M23's `N = 23`), both halves reduced modulo `I_d` before
echelonizing; `dim I_d = Binom(d+1,3) + Binom(d,3) - Binom(d-2,3)` is 5
already at `d = 3`.

**The cubic is isolated by exact linear algebra**: it is defined only
modulo `Q`, so the 5-dimensional degree-3 kernel is reduced modulo an RREF
basis of `Q*{x,y,z,1}` in monomial coordinates and the survivor RREF'd.
Considered and rejected: an orthogonal projection, which is a
transcendental combination of the `K`-rational vectors and unrecognizable
at any precision (in the M23 work it took the cubic from height 68,
saturated, to 17).

**Hyperelliptic genus 4** needs no new code: `TriangleHyperellipticTest`
routes it to the existing path, and `TriangleGenus4Test` also recognizes
it on its own (three quadrics instead of one).  The one obstacle was the
`DegreeBound` trap (4).

## 2. The representative of `(A, B)`

**Decision.** Tuned, as in genus 3: walk the vanishing order of `B` at `P`
from `6d - N - 4` until the reduced, echelonized solution space has one
row.  The RREF row is kept as `Representative := "RREFRow"`.

**History.** The spec of 2026-08-25 prescribed the RREF row, which is what
the four degree-9 reference scripts in M23-recompute used and were
verified with.  On the morning of 2026-11-11, before implementing, this
was changed to tuned on the strength of the genus-3 corrections
(`RESPONSE-genus3-corrections.md` §2).  The first measurement (9T27
alone) then favoured the RREF row and the default was switched to it; the
second (9T25) reversed that; Sam's call was tuned in both genera.

**Measured** (centred pivot, every map verified by `BelyiMapSanityCheck`;
height = most digits in any numerator or denominator of the answer):

| case | prec | tuned | RREF row |
|---|---|---|---|
| genus 3, KMSV 5.27, degree 7 | 40 | 7, passes | 9, passes |
| genus 3, degree 8 cyclic, one cycle | 50 | 1, passes | rescaler error: no constant term |
| genus 3, degree 8 cyclic, two cycles | 50 | 2, passes | rescaler error: no constant term |
| genus 3, 9T27-[9,9,3] | 60 | 9, passes | 18, fails |
| genus 3, 9T27-[9,9,3] | 40 | 9, passes | not measured |
| genus 4, 9T25 | 40 | 9, passes | hung in the divisor check |
| genus 4, 9T25 | 60 | not run | 23, hung in the divisor check |
| genus 4, 9T6 | 40 | 1, passes | not run |
| genus 4, 9T27 | 60 | 17, fails | 12, passes |
| genus 4, 9T27 | 80 | 17, passes | 12 |

Tuned passed every case at some precision with worst case 17; the RREF
row won once, on the genus-4 9T27 by five digits, and lost or broke
everywhere else, worst case 23.  Neither rule picks a small element: both
pick a corner of the `(6d - N - 3)`-dimensional space decided by something
unrelated to height (a vanishing order, or which monomials are pivots), so
which corner is smaller is an accident of the passport.  A second effect
is folded in: `lambda` is read from the map's coefficients, so the
representative changes `lambda` by an algebraic factor that multiplies
into the curve as well (on 9T25 the cubic went from 9 to 20 digits when
only the representative changed).

## 3. The normalizing pivot

**Decision.** Centred on each group's weight range
(`rescale_ind := "Centred"`, selected by `Pivot := "Centred"`, the
default), for quadric, cubic, `A` and `B`.  The rescaler is handed the
quadric alone as the curve; the cubic, which carries its own scalar, is
rescaled by the same `lambda` and normalized by its own centred pivot
afterwards.

**Considered.** The genus-3 code's constant-term pivot, inherited at first.

**Measured** (9T27, prec 80, every map verified; heights of quadric,
cubic, A, B):

| pivot | representative | quadric | cubic | A | B |
|---|---|---|---|---|---|
| centred | tuned | 7 | 13 | 13 | 17 |
| centred | RREF row | 3 | 5 | 12 | 11 |
| constant term | tuned | 12 | 21 | 21 | 21 |
| constant term | RREF row | 4 | 6 | 14 | 13 |

With the constant-term pivot the tuned 9T27 map was unrecognizable at prec
60 AND 80 -- the recognizer over `Q` reaches about prec/4 digits per
numerator and denominator and has no residual gate, so it returned a
wrong `B` and the wrong map sat in the divisor check for a quarter of an
hour.  With the centred pivot it recognizes at 80 and the check takes two
seconds.  This was the larger of the two effects, in both genera.

## 4. `DegreeBound` fallback

**Decision.** `TriangleRecognizeAlgebraicCoefficients` no longer errors
when `MakeK` finds no field of the passport-size degree: it falls back to
smaller degrees.  Passport members related by permuting `0, 1, oo` rather
than by Galois (cyclic covers; 9T1, 9T25) are each defined over a smaller
field.  9T25's test exercises it; 9T1's passes `DegreeBound := 1` as the
spec prescribed.

**Superseded in part.** The original fallback accepted `Q` on the first
five coefficients, which the review of the g4 PR showed to be wrong (9T6
with `DegreeBound := 4`: the curve is over `Q`, the map is not).  The
fallback is now propose / verify -- `Q` gated on every coefficient being
real and fitting at degree 1, then each smaller degree, every candidate
verified on all coefficients before acceptance, with height gates graded
two digits below the phony floor of an explicit LLL lattice.
`Doc/SPEC-degreebound-fallback.md` (with its §7 implementation notes) is
the design of record; `test_degreebound_fallback.m` and the three genus 2
tests `test_genus2_fallback_*.m` are its regression tests.

**Calibration (measured 2026-11-13/14).**  The gate comment in
`recognition.m` points here.

- *Relations are found on an explicit lattice*, rows
  `[e_i | round(10^q Re x_i) | round(10^q Im x_i)]`, not with Magma's
  `PowerRelation` / `LinearRelation`.  Those work at an undocumented
  reduced internal precision: at precision p their phony relations among
  two numbers come out at about p/4 digits (`LinearRelation`) and 3p/8
  (`PowerRelation`), where a lattice at full scale gives p/2.  The floor
  has to be known for a gate to be placed under it.
- *The scale is q = 4p/5.*  Compared with the recognized exact values,
  the nontrivial coefficients carry 41-42 correct digits of 50 on
  7T6-[7,7,6] (genus 2, Q(sqrt 7)) and 33-34 of 40 on 9T6 (genus 4,
  Q(sqrt -3)), curve and map alike: a flat loss of about a fifth, with no
  head-to-tail gradient.  A lattice scaled past the accuracy stretches a
  genuine relation of height h to length h times the excess and loses it.
- *The phony floor* is 10^(q/n) for a relation among n numbers (a degree-m
  minimal polynomial: n = m+1; a fit over an O_K basis of degree m:
  n = m+1), scattering about a digit either side.  *Gates sit two digits
  below it*, flat in position since the accuracy is.  Half the floor, the
  spec's first figure, rejected three of four real maps.
- *Genuine heights seen:* 7 digits over Q (9T25, p = 40, centred pivot;
  floor 16); 9.4 and 12.4 digits over Q(sqrt 7) and Q(sqrt 21)
  (7T6-[7,7,6], genus 2, last-entry pivot; p = 50 and 60, floors 13.3 and
  16); a 13.4-digit minimal polynomial over Q(i) (7T7-[7,4.3,4.3]), which
  p = 50 cannot separate from phony and p = 60 (gate 14) can.
- *Every coefficient, the leading one included, goes through the same
  fit*, ungated once the field is settled.  The scalar `RecognizeOverK`
  returned a leading coefficient off by 3e-24 on 60-digit input for
  7T6-[7,7,6]-b, where the lattice fit is right to 8e-41; the sanity
  check caught it as a hard error on a recognizable map.
- *A tail failure does not abort the ascent.*  On 7T7-[7,4.3,4.3]-d a
  coefficient in the quadratic subfield of the quartic field proposed
  Q(sqrt -3), which fit 12 coefficients of 19: indistinguishable from a
  precision failure on the right field.  Any failure rejects the
  candidate; exhausting every degree reports the best partial fit.

## 5. Tests

| test | prec | field | group | time |
|---|---|---|---|---|
| `test_genus4_hyp_9T1.m` | 40 | Q | fast | 79-153 s |
| `test_genus4_nonhyp_9T25.m` | 40 | Q | fast | 63-107 s |
| `test_genus4_nonhyp_9T6.m` | 40 | Q(sqrt-3) | fast | 69-110 s |
| `test_genus4_nonhyp_9T27.m` | 80 | Q | RUNSLOW | 369-689 s |

Full suite green with `RUNSLOW=1` on Magma 2.29-8 (laptop), 2026-11-11:
1120 s in all, of which 9T27 took 314 s; the fast group is 548 s.

9T27 is gated because its time alone outweighed the rest of the suite;
9T1 is NOT gated, being the only hyperelliptic genus-4 test.  9T32
(passport size 48, prec 100 in the reference computation) has no test:
Sam's call, too slow to be useful even under RUNSLOW.  9T33 (passport
size 837) is out of reach.  All assertions are on ramification through
`BelyiMapSanityCheck`.

## 6. Out of scope

M23 (degree 23, genus 4): its map has heights of 300-400 digits and was
computed exactly by CRT in M23-recompute (`phi_crt.m`); no numerical
representative is within reach.  The open items of the genus-3 ADR §5
apply here too.
