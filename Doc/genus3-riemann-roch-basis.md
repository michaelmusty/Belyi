# Genus 3, non-hyperelliptic: which space, which basis, and where each step happens

*What `Code/genus3nonhyperelliptic.m` and the genus-3 branch of
`Code/recognition.m` actually compute in, and why. Written after reading the
code, not from the design notes.*

---

## 1. Short answer

The Belyi map is written as `phi = lc * (-A)/B` where `A` and `B` are
**polynomials in the affine plane coordinates**, expanded in **plain monomials**
`x^a * y^b` with `a + b <= d`. No `L(m*P)` basis is constructed anywhere.

    N := Degree(Parent(sigma[1]));    // degree of the Belyi map
    d := Ceiling((N+5)/4);            // degree of the forms A, B
    dimI := Binomial(d-2, 2);         // dim I_d

with `Genus3NonHyperellipticMonomials(d)` returning the exponent pairs `[a,b]`,
`a + b <= d`, so `Binomial(d+2,2)` of them. The coordinates are

    x = f_1/f_3,   y = f_2/f_3

on the patch `f_3 != 0`, where `f_1, f_2, f_3` is the echelonized basis of
`S_2(Gamma)`. A canonical genus-3 non-hyperelliptic curve is a smooth plane
quartic, so these are coordinates on `P^2` and the `x^a y^b` with `a+b <= d`
are exactly the degree-`d` forms in `(f_1, f_2, f_3)` dehomogenized.

## 2. The Riemann-Roch content, which is implicit rather than imposed

On a plane quartic the canonical class **is** the hyperplane class `H`:
`deg H = 4 = 2g-2`. So degree-`d` forms are `L(dH)`, of degree `4d`.

Writing `phi = -A/B` with both of degree `d` forces

    B in H^0(dH - phi^*(infinity))

-- `B` must vanish on the polar divisor of `phi`, of degree `N`.

**This has to be argued on the HOMOGENEOUS forms, not the affine ones**, and it
is worth being careful because the obvious objection -- couldn't the numerator
carry a pole at a point where `B` fails to vanish? -- is right about the affine
picture. The affine `A(x,y)` *does* have poles: along the line at infinity
`f_3 = 0`.

Write `Atil, Btil` for the degree-`d` forms in `(f_1, f_2, f_3)`, so that
`A = Atil/f_3^d` and the `f_3^d` cancels in the ratio: `phi = -Atil/Btil`. As
sections of `O(d)` both have **effective** divisors of degree `4d` -- a form
has no poles anywhere, so a pole is not something the numerator can supply.
Pointwise at a pole `Q` of `phi` of order `m`,

    div(Atil)(Q) - div(Btil)(Q) = -m   and   div(Atil)(Q) >= 0
    =>  div(Btil)(Q) >= m

so `Btil` vanishes on all of `phi^*(infinity)`. The affine numerator's poles are matched exactly by the affine
denominator's, so they cancel and cannot absorb a pole of `phi` at a finite
point.

**Why they cancel even when `A` and `B` have different affine degrees.** Both
are drawn from the SAME monomial set, `Genus3NonHyperellipticMonomials(d)`, all
`[a,b]` with `a + b <= d`; and homogenization sends

    x^a * y^b  |-->  f_1^a * f_2^b * f_3^(d-a-b)

to degree **exactly `d`**, padding with `f_3`. So "affine of degree at most `d`"
and "homogeneous of degree `d`" are in bijection, and `Atil`, `Btil` are both
degree-`d` forms whatever their individual affine degrees happen to be. The
`f_3^d` cancels because both are homogenized to the same `d`, not to their own
degrees. If `A` has affine degree 2 and `B` degree 4 with `d = 4`, then `Atil`
simply carries a factor `f_3^2` -- still a form, still an effective divisor,
argument unaffected.

The converse holds too, which is what makes the correspondence exact: if
`div(Btil) >= phi^*(infinity)` then `div(-phi*Btil) >= phi^*(0) >= 0`, effective
of degree `4d`, so `Atil` is a section of `O(d)`.

Checked on 9T27, against the code's OWN `A` and `B` -- read from
`TriangleExactBelyiMapNumeratorCoefficients` and
`TriangleExactBelyiMapDenominatorCoefficients`, and confirmed to satisfy
`phi = lc*A/B` -- and NOT against `Denominator(phi)`, which is Magma's normal
form and a different representative (it prints as a degree-2 polynomial in `xq`
with coefficients of degree 9 in `yq`, nothing like a degree-4 form; an earlier
draft of this note checked that by mistake and got the right verdict for the
wrong object). `phi` has a single polar place, of residue degree 3 and pole
order 3 -- total 9 = N, matching `sigma_inf` of cycle type `3^3` -- and `B`
vanishes there to order exactly 3.

Note this example does not exercise the unequal-degree case: `A` and `B` both
come out of affine degree 4. That case is covered by the argument above, not by
a test. **This condition is never
imposed directly.** It is implied by solving the joint system

    phi*B + A = 0

for a pair `(A, B)` of degree-`d` forms, which is what the code does. That is
worth stating plainly because it is the reason the construction works for
*any* `sigma_0`, with no assumption that it is a single `N`-cycle: a series
identity at one point is a function identity, so nothing about the other
points above `0` or `infinity` needs to be visible to the expansion.

When `dH - phi^*(infinity)` is nonspecial,

    h^0(dH - phi^*(infinity)) = (4d - N) - g + 1 = 4d - N - 2.

The choice `d = Ceiling((N+5)/4)` is what makes nonspeciality automatic:
`4d >= N + 5`, hence `4d - N >= 5 > 4 = 2g-2`. It also explains
`dimI = Binomial(d-2, 2)`: `I_d` is the quartic times the degree-`(d-4)` forms.

| case | N | d | 4d-N | h^0 | start j | dim I_d |
|---|---|---|---|---|---|---|
| KMSV 5.27 | 7 | 3 | 5 | 3 | 2 | 0 |
| C_8 degree 8 | 8 | 4 | 8 | 6 | 5 | 1 |
| BelyiDB 9T27 | 9 | 4 | 7 | 5 | 4 | 1 |

## 3. The `j`-condition

`h^0 >= 3` always, so the solution space is never 1-dimensional on its own and
there would be a representative to choose -- the situation that produced
~408-digit coefficients on the genus-4 M23 map. The code removes the choice by
demanding that `B` vanish harder at the expansion centre `P`:

    ord_P(B) >= jvan,     cutting to H^0(dH - phi^*(infinity) - jvan*P)

and tuning `jvan` until the space is exactly 1-dimensional. The start point is
the nonspecial prediction, `4d - N - 2 - j = 1`:

    jvan := Max(0, 4*d - N - 3);

The condition itself is read off series coefficients -- the first `jvan`
strided coefficients of `B`'s series must vanish -- so it costs nothing beyond
what the stage already has.

### Termination

The loop moves in **both** directions:

    if #hrows eq 1 then found := true;
    elif #hrows eq 0 then jvan -:= 1;   // over-constrained: back off
    else jvan +:= 1;                    // still too big: tighten
    end if;

In exact arithmetic this terminates, and for a stronger reason than "it can go
either way": **it never reverses direction.** Let `f(j)` be the true dimension.
Then `f` is non-increasing, and `f(j) - f(j+1)` is `0` or `1`, because
imposing one extra linear condition drops a dimension by at most one. The unit
step is what does the work -- `f` cannot jump over the value `1`. From `f = 2`
the next value is `2` or `1`, never `0`. So:

- from `f(j) > 1` the loop increments and `f` weakly decreases; since `f -> 0`
  eventually and cannot skip, it passes **through** `1` and stops;
- from `f(j) = 0` it decrements and `f` weakly increases toward `f(0) >= 1`;
  again it cannot skip, so it hits `1`.

The two branches exist to pick the direction from a start point that may be on
either side, not to hunt back and forth. The number of steps is at most about
`4d`.

**Numerically there is no such guarantee**, and that is what the cap is for:

    error if tries gt 4*d + 6,
        "the vanishing order at P did not settle on a 1-dimensional solution
         space after %o tries; raise prec";

`#hrows` is a numerical rank at tolerance `10^(-prec/2)` (with a further
`10^(-prec/3)` guard on the reduced rows), and an *estimated* dimension need
not obey the unit-step property. A marginal singular value can make the
observed dimension read `2` at one `jvan` and `0` at `jvan+1`; the walk then
decrements, reads `2` again, increments, and oscillates. The cap converts that
into an error instead of a hang, and its message names the right remedy:
an oscillation of that kind really is a precision symptom.

So: **terminating for mathematical reasons, capped for numerical ones.** If the
cap ever fires, the diagnosis is a rank decision at the tolerance boundary, not
a logic error in the walk.

## 4. Numerical stage vs exact stage

Everything above is **numerical**, inside
`TriangleGenus3NonHyperellipticNumericalCoefficients`, working on complex power
series in `w`. In order:

1. `x_CC, y_CC` from the echelonized basis, built as `hyperelliptic.m` builds
   its `x_CC`, `y_CC`.
2. `I_d` as the numerical kernel of the monomial series; its dimension is
   asserted against `Binomial(d-2,2)` rather than trusted.
3. The quartic itself, from the degree-4 monomials.
4. The joint system `rows := Wphi cat serd`, where `serd` are the `A`
   monomials and `Wphi` is `phi` times a basis of the `jvan`-vanishing
   subspace. Its kernel is the pairs with `phi*B + A = 0`.
5. Both halves reduced modulo `I_d` **before** echelonizing. The order is not
   optional: reducing afterwards gives a different and far larger
   representative -- on the genus-4 M23 map that single swap moved recognition
   from 1 of 11 coefficients to 8 of 8.
6. A residual check that `phi = -A/B` holds on the curve to full precision.

The **exact** stage is the genus-3 branch of `TriangleMakeBelyiMap` in
`recognition.m`. It receives recognized coefficients indexed by the *same*
`Genus3NonHyperellipticMonomials` ordering -- which is why that ordering lives
in one place -- and assembles:

- the curve, by homogenizing `x^a y^b` as `uq0^a * uq1^b * uq2^(4-a-b)`, so
  that `uq0/uq2 = x` and `uq1/uq2 = y`, giving a plane quartic in `P^2`;
- the map, as `phi = lc * (-A)/B` with `A` and `B` written over the function
  field generators `xq, yq` in the same monomials.

It then checks `IsNonsingular(X)`, `Genus(X) eq 3`, and
`BelyiMapSanityCheck`. Those checks are the real safety net for section 3: the
`j`-walk is **not** self-certifying, and a wrong numerical rank decision is
caught here rather than there.

## 5. Why not an `L(m*P)` basis

MSSV section 6.3 reads `phi_0 in L(t*P)`, `phi_inf = phi_0/phi in L((s+t)*P)`,
and `hyperelliptic.m` implements exactly that. The difference is the **search
space**, not the output format: `hyperelliptic.m` also ends up with polynomials
in `x, y`, because its `L(m*infinity)` basis elements *are* monomials in `x`
and `y`. What it gains is that the span is already pole-order-bounded, so its
kernel is 1-dimensional by construction and no `j`-walk is needed.

That works there because the hyperelliptic model hands it `x` and `y`, global
functions whose polar divisors are known a priori to sit at infinity. A plane
quartic has no such coordinates at a general `P`: "poles only at `P`" is a
condition about the other three points where a line through `P` meets the
curve, and a single power series at `P` carries no information about them.

It *is* obtainable from the plane model -- `P = (1:0:0)` exactly, since the
basis is echelonized so `f_1(P) != 0` while `f_2, f_3` vanish (confirmed on
KMSV 5.27, where the measured `svals` are `[0,1,2]`) -- but the residual of a
line through `P` is a numerical root-finding problem on the quartic, with
multiplicity detection and near-degenerate vanishing conditions. That is the
blocker; the linear algebra around it is routine.

**The open question is heights, and it is empirical.** This construction has
the same shape as the genus-4 M23 one whose coefficients reached ~408 and ~295
digits. The `j`-walk removes the representative choice that caused that -- a
1-dimensional kernel has nothing to pick -- but "canonical" does not imply
"small", and forcing `B` to vanish to high order at `P` is a strong constraint
that could inflate coefficients instead. On what has been run it is fine:
9T27's curve has 12-digit coefficients and its map 2-to-9-digit ones, and KMSV
is smaller still.

The tell to watch for is a passport where the *curve* recognizes cleanly but
the map does not, with heights that do not shrink as precision rises. That is
the signature of an inflated representative rather than of insufficient
precision -- and note that the reverse pattern is what 9T27 shows at
`prec := 40`, where the map comes back with ~100-digit numerators and
denominators that collapse to 12 digits at `prec := 60`. Before doing the
root-finding work for `L(m*P)`, find a case where heights are actually the
problem; without one, it is effort against no demonstrated payoff.
