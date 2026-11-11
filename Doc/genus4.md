# Belyi maps in genus 4, non-hyperelliptic

Companion notes for `Code/genus4.m` and for the changes it required in
`Code/belyi_main.m`, `Code/recognition.m`, `Code/hackobj.m` and `Code/spec`.
Read `Doc/genus3-nonhyperelliptic.md` first: the genus-4 code is that
construction one dimension up, and only what differs is recorded here.
The decisions behind it, with the alternatives and the measurements, are
in `Doc/adr-genus4.md`.

## What was added

| file | change |
|---|---|
| `Code/genus4.m` | new: `Genus4Monomials`, `Genus4IdealDimension`, `TriangleGenus4Test`, `TriangleGenus4NumericalCoefficients` |
| `Code/spec` | lists `genus4.m` |
| `Code/hackobj.m` | attributes `TriangleIsGenus4Canonical`, `TriangleGenus4FormDegree` |
| `Code/belyi_main.m` | genus 4 non-hyperelliptic branch after the genus-3 one; the refusal moves to genus `> 4` |
| `Code/recognition.m` | `TriangleRecognizeAlgebraicCoefficients` and `TriangleMakeBelyiMap` widened; the former gains a fallback from the passport-size `DegreeBound` down to `Q`; `TriangleRescaleCoefficients` gains `rescale_ind := "Centred"` |
| `Tests/test_genus4_hyp_9T1.m` | genus 4 but HYPERELLIPTIC: checks the dispatch does *not* take this branch |
| `Tests/test_genus4_nonhyp_9T25.m` | 9T25-[9,9,9], over `Q`, trivial `Aut`; exercises the `DegreeBound` fallback |
| `Tests/test_genus4_nonhyp_9T6.m` | 9T6-[9,9,9], over `Q(sqrt(-3))`, `Aut` of order 3: the weight-gcd branch |
| `Tests/test_genus4_nonhyp_9T27.m` | 9T27-[9,9,9], over `Q`, `prec := 60` |
| `Tests/run_tests.sh` | runs 9T1, 9T25 and 9T6 in the fast group; 9T27 under `RUNSLOW` |

The test triples and the precisions come from the degree-9 genus-4 work in
`M23-recompute` (`pass9.m`, `belyi_9T25.m` and its siblings), where each of
these maps was first computed and its ramification verified.

## The construction

- The canonical model of a non-hyperelliptic genus-4 curve is the
  intersection of a **unique quadric** `Q` and a **cubic** `C` in `P^3`, with
  coordinates the echelonized basis `f_1, ..., f_4` of `S_2(Gamma)`.  Affine
  coordinates `x = f_1/f_4`, `y = f_2/f_4`, `z = f_3/f_4` on the patch
  `f_4 != 0`; the canonical class is the hyperplane class, of degree 6.
- `TriangleGenus4Test` finds `Q` as the 1-dimensional kernel of the ten
  degree-2 monomial series, and `C` from the 5-dimensional kernel of the
  twenty degree-3 ones.  **`C` is defined only modulo `Q`**: the kernel is
  `Q*{x,y,z,1}` plus `C`, and `C` is isolated by reducing the kernel modulo an
  RREF basis of the multiples of `Q`, in monomial coordinates, then RREF-ing
  what survives -- exact linear algebra, never an orthogonal projection,
  which is a transcendental combination of the `K`-rational vectors.
- A degree-2 kernel of dimension **3** means the curve is hyperelliptic (the
  canonical image is a rational normal cubic, on three quadrics).  The test
  reports that and returns `false`; in practice `belyi_main.m` has already
  routed such a curve to the hyperelliptic path, which handles genus 4
  without new code (`Tests/test_genus4_hyp_9T1.m`).
- The map is `phi = -A/B` with `A, B` forms of degree `d`, the least with
  `6d - N > 6`, so that `H^0(dH - phi^*(oo))` is nonspecial of dimension
  `6d - N - 3`.  `dim I_d = Binom(d+1,3) + Binom(d,3) - Binom(d-2,3)` is 5
  already at `d = 3`; both halves of every kernel vector are reduced modulo
  it **before** echelonizing.
- **The representative of `(A, B)`.**  `TriangleGenus4NumericalCoefficients`
  takes `Representative := "Tuned"` (the default): require `ord_P(B) >= j`
  and walk `j` until the reduced, echelonized space has one row, so that
  nothing is chosen -- the genus-3 construction.  Or `"RREFRow"`: impose no
  vanishing at `P`, reduce the whole `(6d - N - 3)`-dimensional solution
  space modulo `I_d`, RREF it in monomial coordinates, take the first row
  whose `B`-part survives -- the reference scripts' method.  Every element
  of that space gives the same map with a different height, and neither
  rule picks a small one: both pick a corner of the space decided by
  something unrelated to height (a vanishing order, or which monomials are
  pivots), so which corner is smaller is an accident of the passport.  The
  default was decided by measurement across every example we have, all
  with the centred pivot, every map verified by `BelyiMapSanityCheck`;
  "height" is the most digits in any numerator or denominator of the
  answer.

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

  Tuned passed every case at some precision with a worst case of 17; the
  RREF row won once, on the genus-4 9T27 by five digits, and lost or broke
  everywhere else, with a worst case of 23.  So tuned is the default in
  both genera, and the genus-4 9T27 test runs at prec 80.  A second effect
  is folded into these numbers: `lambda` is read from the map's
  coefficients, so changing the representative changes `lambda` by an
  algebraic factor that multiplies into the curve too (on 9T25 the cubic
  went from 9 to 20 digits when only the representative changed).  The
  principled fix would be to recognize a basis of the whole solution space
  over `K` and LLL-reduce it for a genuinely short element; not done.  The
  sanity check is the referee for either option.
- The curve has **two groups**, each defined up to its own scalar.
  `TriangleRescaleCoefficients` divides the whole curve list by one pivot,
  which normalizes the quadric; the cubic is then divided by a pivot of its
  own.
- **Pivots are centred on the weight range** (`Pivot := "Centred"`, the
  default, which passes `rescale_ind := "Centred"` to
  `TriangleRescaleCoefficients`; `"LastNonzero"` is the old constant-term
  convention).  The rescaler is handed the quadric alone as the curve, and
  the cubic is rescaled by the same `lambda` and normalized by its own
  centred pivot afterwards.
  After the torus is undone each coefficient is the ratio to its group's
  pivot times an algebraic factor raised to the weight offset from the
  pivot, so the height grows with that offset, and an extreme pivot roughly
  doubles the worst case.  This was measured, not assumed.  On 9T27 at
  prec 80 (heights of quadric, cubic, A, B):

  | pivot | representative | quadric | cubic | A | B |
  |---|---|---|---|---|---|
  | centred | tuned | 7 | 13 | 13 | 17 |
  | centred | RREF row | 3 | 5 | 12 | 11 |
  | last nonzero | tuned | 12 | 21 | 21 | 21 |
  | last nonzero | RREF row | 4 | 6 | 14 | 13 |

  With the extreme pivot the tuned map was out of reach at prec 60 AND 80
  (the recognizer over `Q` reaches about prec/4 digits per numerator and
  denominator, and has no residual gate), and the wrong map then sat in the
  divisor check for a quarter of an hour.  With the centred pivot it
  recognizes at 80 and the sanity check takes two seconds.  The curve's
  heights move too, because `lambda` is read from the map's coefficients
  and the Bezout combination changes with them.
- `TriangleMakeBelyiMap` homogenizes with `uq3`, builds
  `Curve(ProjectiveSpace(K, 3), [Q, C])`, checks it is nonsingular of genus
  4, and forms `phi = lc * FF!(-A/B)`: the ratio of two forms of equal degree
  coerces into the function field of a curve in `P^3`.

## The `DegreeBound` fallback

`BelyiMap` bounds the degree of the field of definition by the passport
size.  That is an upper bound, not the degree: when passport members are
related by the `S_3` action on `{0, 1, oo}` rather than by Galois -- a cyclic
cover, say -- each member is defined over a smaller field, and `MakeK` finds
no field of the full degree.  Previously that was a hard error ("Unable to
create number field!").  Now `TriangleRecognizeAlgebraicCoefficients` retries:
first `Q`, accepted only if every coefficient is real to working precision
and the first few nonzero ones satisfy degree-1 relations of height below
`10^(prec/4)` (a spurious degree-1 fit has height `~10^(prec/2)`); then
proper fields of each smaller degree.  The sanity check remains the referee.
9T25 (passport size 4, over `Q`) exercises this; 9T1 would too, but its test
passes `DegreeBound := 1` as the spec prescribes.

## What was verified

All four fast tests were run on Magma 2.29-8 (laptop) before this was
committed, through `BelyiMap` and its `BelyiMapSanityCheck`:

| test | prec | field | BelyiMap time |
|---|---|---|---|
| 9T1 (hyperelliptic path) | 40 | Q | 153 s |
| 9T25 | 40 | Q | 107 s |
| 9T6 | 40 | Q(sqrt(-3)) | 110 s |
| 9T27 | 80 | Q | 314 s in the suite (RUNSLOW) |

Full suite green with `RUNSLOW=1`, 1120 s; fast group 548 s.

9T27 is gated behind `RUNSLOW` because its 369 s outweighed the rest of the
suite; 9T1 stays in the fast group because it is the only hyperelliptic
genus-4 test.  9T32 (passport size 48, over `Q(sqrt(-3))`, prec 100 in the
reference computation, where its heights were at most 20) has no test: at
prec 100 the series stage alone would take a quarter of an hour or more,
too slow to be a useful test even under `RUNSLOW`.  9T33 (passport size
837) is out of reach.

## Known limitations

- Reach, not correctness: the map must have height within what LLL at the
  chosen precision certifies.  M23 (degree 23, genus 4) does not; its map
  was computed exactly by CRT instead (`M23-recompute/phi_crt.m`).
- `TriangleRescaleCoefficients` still needs a nonzero weight-zero
  coefficient -- the constant term -- in `A` or `B`.  Not hit on any test.
- The weight-gcd root of unity (`lambda^(1/gcd)`) is resolved downstream by
  the sanity check, as in genus 3.  On 9T6 (gcd 3) every weight is divisible
  by 3, so no branch choice ever arises.
