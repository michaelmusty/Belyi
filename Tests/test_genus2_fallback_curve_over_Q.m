// The DegreeBound fallback in the exact shape of the bug the g4 PR review
// found: 7T7-7_4.3_4.3-c from the LMFDB (genus 2, degree 7, passport of
// size 9 splitting into Galois orbits of sizes 1, 2, 2, 4).  This orbit's
// CURVE is defined over Q -- all 12 curve coefficients, which lead the list
// of coefficients to recognize, are rational -- while the MAP needs Q(i).
// The old fallback accepted Q on the first five coefficients; the reality
// check on every coefficient rejects it.
//
// The triple is as the LMFDB gives it (shared convention
// sigma[3]*sigma[2]*sigma[1] = 1).
//
// PRECISION.  prec := 60.  The minimal polynomial over Q(i) that proposes the
// field has height 2.5e13, which prec 50 (phony floor 13.3 digits) cannot
// tell from phony and prec 60 (floor 16, gate 14) can.

AttachSpec("Code/spec");

S7 := Sym(7);
sigma := [S7 | [2,3,4,5,6,7,1], [4,6,1,5,3,7,2], [6,3,7,5,1,4,2]];
assert sigma[3]*sigma[2]*sigma[1] eq Id(S7);

Gamma := TriangleSubgroup(sigma);
assert Genus(Gamma) eq 2;
assert #PassportRepresentatives(sigma : Pointed := true) eq 9;

cbin := GetEnv("POWSER_ARNOLDI_BIN");
if cbin eq "" then cbin := "powser_arnoldi"; end if;
retc := System(Sprintf("command -v %o > /dev/null 2>&1 || test -x %o", cbin, cbin));
powseral := (retc eq 0) select "CArnoldi" else "Arnoldi";
printf "PowserAl := %o\n", powseral;

t0 := Cputime();
X, phi, Gamma := BelyiMap(Gamma : prec := 60, PowserAl := powseral);
printf "BelyiMap took %o s\n", Cputime(t0);

K := BaseRing(X);
assert Degree(K) eq 2;
assert Discriminant(Integers(K)) eq -4;                   // K = Q(i)
// diagnostic, not asserted: in the LMFDB's model the curve is over Q; in
// this package's normalization (last-entry pivot, torus undone by lambda)
// the split between rational and irrational coefficients may differ
cc := Gamma`TriangleExactCurveCoefficients;
mc := Gamma`TriangleExactBelyiMapNumeratorCoefficients cat Gamma`TriangleExactBelyiMapDenominatorCoefficients;
printf "rational coefficients: curve %o of %o, map %o of %o\n",
  #[c : c in cc | IsCoercible(Rationals(), c)], #cc, #[c : c in mc | IsCoercible(Rationals(), c)], #mc;

assert Genus(X) eq 2;
assert BelyiMapSanityCheck(sigma, X, phi);
assert Degree(phi) eq 7;

print "ALL TESTS PASSED";
quit;
