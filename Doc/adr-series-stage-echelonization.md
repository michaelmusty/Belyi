# ADR: echelonization and kernel conditioning in the series stage

*Decision record for three changes to shared numerical code, made
2026-11-12 during Stage 0 of `Doc/SPEC-genus5plus.md` (§8), where the
`11T6` passport (M11, degree 11, genus 5) failed in ways no previous
passport had.  Two of the changes are in code every genus uses
(`Code/powser_iter_arfed.m`, `Code/serieskernel.m`); the third is the
row convention of `Code/petri.m`, prescribed onward for
`genus-general.m`.  The hunt itself, including the false trails, is in
§8 of the spec; this file records what was decided and why.*

## 1. Context

`PowerSeriesBasis` finds the weight-2 forms of `Gamma` as fixed vectors of
a linear operator on power-series coefficients (Arnoldi in Magma or in
the C solver, or a dense SVD in the `"Full"` branch), then echelonizes
the `dim` vectors it gets back so that form `i` vanishes to a strictly
higher order at the expansion centre than form `i - 1`, with leading
coefficient 1.  Every downstream computation -- the hyperelliptic test,
the plane quartic, the quadric-and-cubic, the Petri classification, the
map -- consumes that echelonized basis.

On `11T6` the echelonized basis was garbage: the identity in coefficients
0-4 plus noise, then entries of `10^22` and up.  The failure was
independent of precision (30, 50, 80), term count (`N = 3000`), solver
branch (C and pure Magma), start vectors, and expansion centre.  Its
signature was the transformation matrix of the echelonization, with
entries of 25, 43 and 72 digits at prec 30, 50, 80: exactly
`1/eps_thresh`.  The dense `"Full"` branch showed the operator's fixed
space is a clean five-dimensional one (singular values `10^-29 ..
10^-27`, then `0.076`), and its raw vectors, inspected directly, are
good forms with orders of vanishing `[0, 1, 2, 3, 5]` at the centre: a
Weierstrass point, gap sequence `{1, 2, 3, 4, 6}`, on a curve with no
automorphism or stabilizer behind it.

## 2. Decision: magnitude-pivoting echelonization (`powser_iter_arfed.m`)

**Was.** `E, T := EchelonForm(M)` on the coefficient matrix, after an
absolute zeroing of entries below `10^(-4/5 prec)`.  `EchelonForm` over a
complex field is exact elimination: in each column it pivots on the first
entry that is not literally zero, with no tolerance.

**Why it broke.** With orders `[0,1,2,3,5]`, column 4 of every raw vector
is a combination of its columns 0-3 to the solver's accuracy
`~eps_thresh`.  After columns 0-3 are eliminated, column 4 holds only
that residue, about `10^-24`; it is not literally zero, so it became the
pivot and every genuine coefficient was divided by it.  The pre-zeroing
cannot help: it runs before elimination, and the residue is created by
elimination.  Sam's first diagnosis -- "a division by a machine zero" --
was the right one.

**Why it never broke before.**  Pivot gaps are normal (every Weierstrass
centre has them) and had occurred many times; what had always
accompanied them were EXACT zeros in the dependent columns, from
symmetry.  At a centre fixed by an automorphism (a Galois cover, where
`Delta` normalizes `Gamma`), or with a nontrivial stabilizer (the stride
`e`), every form's expansion is supported on one residue class of
exponents, so the non-pivot columns are structurally empty and
`EchelonForm` has nothing to divide by.  The trigonal `11T1` curve, orders
`[0,1,2,5,6]`, survived the old code for exactly that reason.  `11T6`
has a Weierstrass centre and no symmetry: coefficient 4 is an honest
nonzero number that is merely dependent.

**Is.**  Gauss-Jordan on `[M | I]` with partial pivoting by largest
modulus, and a column skipped when its largest remaining entry is below
`tolm = scl * 10^(-prec/2)`, `scl` the largest entry of the matrix.  The
transformation `T` has the same meaning as before (`T * M = E`) and is
applied to every neighbourhood's series exactly as before.  Because
columns are scanned in order and each form pivots at the first column
where it has genuine content, the pivot columns are the orders of
vanishing at the centre; they are printed (`Echelonize: pivots at
orders of vanishing [...] , max |T| = ...`), and `max |T|` is a
conditioning readout: about 10 on healthy bases, `10^24` on the broken
ones.  Fewer than `dim` pivots is an error naming the pivots found,
instead of a silently wrong basis.

**Judgment calls.**  `10^(-prec/2)` sits between the solver's accuracy
`~10^-(prec-6)` and the order-one genuine entries, with wide margins at
every precision in use.  `scl` is taken over the whole matrix, tails
included (about `10^5` at `n ~ 1600` on healthy bases at prec 30), so the
effective threshold is near `10^-10`; a basis with tails near `10^20`
would push it above genuine pivots and fail LOUDLY with the dependency
error, at which point `scl` should be measured over the early columns
only.  Cost is negligible.

**Considered and rejected.**  Raising `prec` (measured: 30, 50, 80 --
the amplification scales with the threshold, never cured).  Zeroing the
first `g` coefficients before `EchelonForm` (the residue does not exist
before elimination, and pivots can lie beyond `g - 1`: `[0,1,2,5,6]`).
An epsilon for `EchelonForm` (there is none).

## 3. Decision, then reversal: column scaling in `SeriesKernel` (`serieskernel.m`)

**Context.**  With the echelonization fixed, `11T6` member 1 passed and
member 2 failed one stage later, in the Petri test's degree-3 kernel:
`NumericalKernel` returned dimension 31 at `eps = 10^-12`, 15 (correct)
at `10^-20`, and "Error in precision in numerical linear algebra" at
`10^(-prec/2)`.  Cause: the affine coordinates `x_i = f_i/f_5` converge
only out to the nearest other zero of `f_5`, which for this member is at
radius about 0.74; their coefficients reach `10^19` within 200 terms and
the degree-3 monomial rows span `10^17` across the 140-column window,
so after row normalization each row is numerically supported on its last
few columns and the SVD cannot see the relations.

**Decision.**  Scale column `n` by `r^n` before the row normalization.
This leaves the left kernel unchanged exactly (`y M = 0` iff `y M D = 0`
for invertible diagonal `D`) and amounts to reading the relation on the
circle of radius `r` instead of radius 1.  `r` is the reciprocal of the
worst row's SUSTAINED growth per column: the largest entry of the last
third of the window against the largest of the first third, over entries
above `eps` times the row's maximum.  It is capped so that
`r^ncols >= eps`, so the scaling can never push a column below the kernel
tolerance (which would leave fewer informative columns than rows and
manufacture kernel vectors).  For rows that do not grow, `r = 1` and
nothing changes.  Every kernel in the package goes through
`SeriesKernel`, so genus 3 and 4 inherit it.

**History of the estimator, kept because each step was a measured
failure.**  (i) Growth from the first literally nonzero entry: the rows
`phi * B` of the map's joint system start with `ord_P(phi)` exact zeros,
arithmetic dust of `10^-19` just before their content gave a growth of
`e^43` per column and `r = 10^-19`, and three genus-3 and genus-4 tests
failed with residual 1.  (ii) Slope from the first significant entry to
the row's maximum: a row rising a hundredfold over its first five columns
then flat read as `e^0.9` per column, held only by the cap.  (iii) The
sustained-growth measure now in place.  With the homogeneous rows of
§4 the scaling no longer engaged on the Petri rows at all.

**Reversal (same day).**  Removed.  With the Petri rows homogeneous, its
only remaining clients were the affine rows of the hyperelliptic test
and of the genus-3 and genus-4 curve and map stages, and on every one of
those it had no measured effect: the hyperelliptic test on 11T6 member 2
passed without it, and so did every genus-3 and genus-4 test.  A
heuristic that needed three attempts to stop breaking things, living in
code every kernel goes through, is a liability with no demonstrated
benefit.  It also pointed the wrong way: the growth it mitigated comes
from dividing by a form, and the fix is to stop dividing (§4), not to
read affine series on a smaller circle.  Should the hyperelliptic test
ever show the symptom -- it divides by `f_2` and `f_g` -- the remedy is
to homogenize its relation `y^2 + u(x) y = v(x)` by clearing those
denominators, so that its rows too are products of forms.  The row
normalization that preceded the scaling stays.  `SeriesKernel` is back to
what it was before 2026-11-12, and the suite and the three Stage-0
controls were rerun on it.

## 4. Decision: homogeneous rows in `petri.m`, and onward

**Was.**  Degree-`d` monomial rows built from the affine coordinates
`x^m = f^m / f_g^d`, inherited from `hyperelliptic.m` through genus 3 and
genus 4.

**Is.**  Rows built as `f_1^(m_1) ... f_(g-1)^(m_(g-1)) f_g^(d - |m|)`:
products of holomorphic forms, convergent on the whole disc.  The
relations are identical (every affine row is the homogeneous one divided
by the single series `f_g^d`), so the coefficient vectors, their indexing
by `CanonicalMonomials`, the RREF, and the affine-convention torus
weights handed to the rescaler (a shift by `-d s_g` per degree, as the
genus-3 notes already state) are unchanged.  Only the poles are gone.

**Why affine was chosen originally.**  The genus-3 documents
(`genus3nonhyperelliptic.m` header "THE TORUS"; `genus3-riemann-roch-basis.md`
§3; `genus3-nonhyperelliptic.md` item 8) chose affine coordinates for
the rescaler's bookkeeping: the weight-zero coefficient is the constant
term affinely but `f_1^d` projectively, which the KMSV quartic lacks; and
`Xgcd` reads the shifted weights.  Those reasons apply to the coefficient
lists handed to the rescaler, which stay affine-indexed, not to how the
series rows are built; the Riemann-Roch document itself argues
correctness on the homogeneous forms.  The hyperelliptic test stays
affine: its model is `y^2 + u(x) y = v(x)` by construction.
`genus-general.m` is to use the homogeneous convention (spec §3 step 0,
§4); genus 3 and 4 could, but work as they are.

## 5. Diagnostics added

- `hyperelliptic.m` (`HypRelationKernel`) and `petri.m` check that the
  echelonized basis vanishes to strictly increasing orders at the centre
  and otherwise error with those orders and "raise prec".  On the old
  code these turned a silent wrong answer (and a crash deep inside
  `NumericalKernel`) into a loud one; on the new code they should never
  fire, and if they do the series stage is the place to look.
- `Code/petri_stage0.m` checkpoints the series per member (`skdir`) and
  fixes the random seed, since `PassportRepresentatives` is not
  deterministic across sessions (three sessions gave three different
  "member 1" triples for `11T6`).

## 6. Verification

Fast suite green after each change (final: 593 s, solver at two
threads).  Stage-0 verdicts, rerun after every change and identical
throughout: `11T5` members 1 and 2 General; `11T6` members 1 and 2
General, orders `[0,1,2,3,5]`; `11T1` `(1,1,9)` hyperelliptic and
`(1,2,8)` Trigonal with three quadrics and two cubics, orders
`[0,1,2,3,4]` and `[0,1,2,5,6]`, the closed forms of spec §7.

| series stage, 11T6 member 1 | terms | time |
|---|---|---|
| prec 30 | 1637 | 128-147 s |
| prec 50 | 2727 | 444 s |
| prec 80 | 4362 | 1538 s |
| prec 30, `"Full"` (dense operator + SVD) | 1637 | 3265 s |

## 7. Lesson

Every wrong theory in the hunt (undeflated Arnoldi sequences, a
one-dimensional fixed space, a wrong operator, forms vanishing to order
5) was read off the ECHELONIZED output.  Nobody looked at a raw solver
vector until the end, and the raw vectors were fine all along.  Save and
inspect the raw intermediate before theorizing about post-processed
output.
