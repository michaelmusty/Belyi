# ADR: Belyi maps in genus 3, non-hyperelliptic

*Decision record for `Code/genus3nonhyperelliptic.m`.  The construction
itself is documented in `Doc/genus3-nonhyperelliptic.md` and
`Doc/genus3-riemann-roch-basis.md`; this file records what was decided,
what else was considered, and what measurement settled it.  Status: the
code is merged (PR #40); the pivot decision (3) was made on the g4 branch,
2026-11-11.*

## 1. Canonical model and coordinates

**Decision.** A non-hyperelliptic genus-3 curve is its canonical plane
quartic.  Work in affine coordinates `x = f_1/f_3`, `y = f_2/f_3` on the
patch `f_3 != 0`, with `f_1, f_2, f_3` the echelonized basis of `S_2`.
The map is `phi = -A/B` with `A`, `B` polynomials of degree
`d = Ceiling((N+5)/4)` in `x, y`, the least `d` making the class
`dH - phi^*(oo)` nonspecial.

**Considered.** A Riemann-Roch basis `L(m*P)` at the expansion point, as
`hyperelliptic.m` uses, which was the original prescription
(`M23-recompute/SPEC-genus3-riemann-roch-fix.md` §3).  Rejected: a plane
quartic has no coordinates whose poles are known to sit at `P` alone, so
`L(m*P)` needs numerical root-finding on the model away from `P` -- a new
and untestable source of fragility -- to buy what the vanishing-order
construction (2) already buys.

## 2. The representative of `(A, B)`

**Decision.** Force the solution space to dimension 1: require
`ord_P(B) >= j` and walk `j` until the reduced, echelonized kernel of the
series identity `A + phi*B = 0` has exactly one row ("tuned").  Nothing is
chosen.  Both halves are reduced modulo `I_d` BEFORE echelonizing.

**Considered.** The first spec (`M23-recompute/HANDOFF-genus3.md` step 6)
said to RREF the whole `(4d - N - 2)`-dimensional space and take the first
row whose `B`-part survives ("RREF row").  Retracted one day later
(`RESPONSE-genus3-corrections.md` §2): every element of that space gives
the same map with wildly different heights, and the genus-4 M23 map showed
what a bad pick costs (a ~408-digit representative of a ~130-digit map).

**Measured** (2026-11-11, centred pivot, every map verified by
`BelyiMapSanityCheck`; height = most digits in any numerator or
denominator of the answer):

| case | prec | tuned | RREF row |
|---|---|---|---|
| KMSV 5.27, degree 7 | 40 | 7, passes | 9, passes |
| degree 8 cyclic, one cycle | 50 | 1, passes | rescaler error: no constant term |
| degree 8 cyclic, two cycles | 50 | 2, passes | rescaler error: no constant term |
| 9T27-[9,9,3] | 60 | 9, passes | 18, fails |
| 9T27-[9,9,3] | 40 | 9, passes | not measured |

Tuned is the smaller representative everywhere in genus 3, and the RREF
row loses the weight-zero coefficient that `TriangleRescaleCoefficients`
cannot do without on the cyclic covers.  Decision confirmed.  (In genus 4
the same comparison is mixed; see `Doc/adr-genus4.md`.)

## 3. The normalizing pivot

**Decision.** Each of quartic, `A`, `B` is divided by a coefficient whose
weight is nearest the CENTRE of that list's nonzero weight range
(`rescale_ind := "Centred"` of `TriangleRescaleCoefficients`, selected by
`Pivot := "Centred"`, the default).

**Considered.** The merged code divided by the last nonzero entry, the
constant term, at one extreme of the weight range -- the convention genus
1, genus 2 and the hyperelliptic path use, where it is left unchanged.
The genus-3 spec §4.3 had asked for a centred pivot: after the torus is
undone each coefficient is `(c_j/c_piv) * alpha^(w_j - w_piv)` for an
algebraic `alpha`, so the height grows with the weight offset from the
pivot, and an extreme pivot roughly doubles the worst case.

**Measured** (2026-11-11, tuned representative, every map verified;
heights of quartic, A, B):

| case | prec | constant-term pivot | centred pivot |
|---|---|---|---|
| KMSV 5.27 | 40 | 4, 2, 3 | 7, 4, 4 |
| degree 8 cyclic (both triples) | 50 | 1-2 | 1-2 |
| 9T27-[9,9,3] | 60 | 12, 12, 12 | 7, 9, 8 |
| 9T27-[9,9,3] | 40 | 10, 10, 10, sanity check FAILS | 7, 9, 8, passes |

On the only hard case the centred pivot cuts the heights by a third and
turns the known prec-40 failure into a pass; on the tiny cases it changes
nothing that matters.  The test for 9T27 stays at prec 60 for margin.

## 4. Tests

`Tests/test_genus3_hyp.m` (dispatch must NOT take this branch),
`test_genus3_nonhyp_deg7.m` (KMSV Example 5.27), `test_genus3_nonhyp_deg8.m`
(cyclic, `dim I_d != 0`, and a `sigma_0` with two cycles),
`test_genus3_nonhyp_9T27.m` (generic, rigid, over `Q`).  All in the fast
group; assertions on ramification, never on coefficients, since any
coefficient-built `lambda` recovers the curve twisted by an algebraic
diagonal.

## 5. Open

Neither representative rule picks a SMALL element of the solution space;
the principled fix is to recognize a basis of the whole space over `K` and
LLL-reduce it.  `lambda` is read from the map's coefficients, so the
curve's heights depend on which `(A, B)` was chosen; they should not.
Whether the centred pivot should become the rescaler's default for genus
1, 2 and hyperelliptic is unmeasured.
