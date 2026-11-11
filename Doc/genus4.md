# Belyi maps in genus 4, non-hyperelliptic

Companion notes for `Code/genus4.m` and for the changes it required in
`Code/belyi_main.m`, `Code/recognition.m`, `Code/hackobj.m` and `Code/spec`.
Read `Doc/genus3-nonhyperelliptic.md` first: the genus-4 code is that
construction one dimension up, and only what differs is recorded here.

## What was added

| file | change |
|---|---|
| `Code/genus4.m` | new: `Genus4Monomials`, `Genus4IdealDimension`, `TriangleGenus4Test`, `TriangleGenus4NumericalCoefficients` |
| `Code/spec` | lists `genus4.m` |
| `Code/hackobj.m` | attributes `TriangleIsGenus4Canonical`, `TriangleGenus4FormDegree` |
| `Code/belyi_main.m` | genus 4 non-hyperelliptic branch after the genus-3 one; the refusal moves to genus `> 4` |
| `Code/recognition.m` | `TriangleRecognizeAlgebraicCoefficients` and `TriangleMakeBelyiMap` widened; the former gains a fallback from the passport-size `DegreeBound` down to `Q` |
| `Tests/test_genus4_hyp_9T1.m` | genus 4 but HYPERELLIPTIC: checks the dispatch does *not* take this branch |
| `Tests/test_genus4_nonhyp_9T25.m` | 9T25-[9,9,9], over `Q`, trivial `Aut`; exercises the `DegreeBound` fallback |
| `Tests/test_genus4_nonhyp_9T6.m` | 9T6-[9,9,9], over `Q(sqrt(-3))`, `Aut` of order 3: the weight-gcd branch |
| `Tests/test_genus4_nonhyp_9T27.m` | 9T27-[9,9,9], over `Q`, `prec := 60` |
| `Tests/test_genus4_nonhyp_9T32.m` | 9T32-[9,9,9], passport size 48, `prec := 100`; `RUNSLOW` only |
| `Tests/run_tests.sh` | runs the first four in the fast group, 9T32 under `RUNSLOW` |

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
- **The solution space is forced to dimension 1**, exactly as in genus 3:
  require `ord_P(B) >= j` and walk `j`, starting from `6d - N - 4`, until the
  reduced, echelonized space has one row.  Nothing is chosen.  (The genus-4
  reference scripts in `M23-recompute` took an RREF row of the
  `(6d - N - 3)`-dimensional space instead, and got away with it only
  because the degree-9 heights are at most ~9; on M23 that choice produced a
  ~408-digit representative of a ~130-digit map.  `M23-recompute`'s
  `SPEC-genus4.md`, revision of 2026-11-11, records the decision.)
- `TriangleGenus4NumericalCoefficients` takes `Representative := "Tuned"`
  (the default, above) or `"RREFRow"`: impose no vanishing at `P`, reduce
  the whole solution space modulo `I_d`, RREF, take the first row whose
  `B`-part survives.  The latter is the reference scripts' method and the
  documented fallback; which representative has the smaller height is an
  empirical question per passport, and the sanity check is the referee for
  either.
- The curve has **two groups**, each defined up to its own scalar.
  `TriangleRescaleCoefficients` divides the whole curve list by one pivot,
  which normalizes the quadric; the cubic is then divided by a pivot of its
  own.
- **Pivots are centred on the weight range** (`Pivot := "Centred"`, the
  default), not the constant term (`"LastNonzero"`, the genus-3 convention).
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
| 9T27 | 80 | Q | 689 s |

9T32 was not run here (prec 100, minutes for the series alone) and is gated
behind `RUNSLOW`.

## Known limitations

- Reach, not correctness: the map must have height within what LLL at the
  chosen precision certifies.  M23 (degree 23, genus 4) does not; its map
  was computed exactly by CRT instead (`M23-recompute/phi_crt.m`).
- `TriangleRescaleCoefficients` still needs a nonzero weight-zero
  coefficient -- the constant term -- in `A` or `B`.  Not hit on any test.
- The weight-gcd root of unity (`lambda^(1/gcd)`) is resolved downstream by
  the sanity check, as in genus 3.  On 9T6 (gcd 3) every weight is divisible
  by 3, so no branch choice ever arises.
