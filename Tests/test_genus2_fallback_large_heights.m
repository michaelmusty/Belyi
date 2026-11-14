// The DegreeBound fallback on a REAL quadratic field with LARGE heights:
// 7T6-7_7_3.2.2-b from the LMFDB (genus 2, degree 7, passport of size 7
// splitting into Galois orbits of sizes 1, 2, 2, 2; this orbit is defined
// over Q(sqrt 21)).  Sibling of test_genus2_fallback_real_quadratic.m.
//
// Its coefficients reach 12.4 digits of height, which prec 50 (phony floor
// 13.3 digits) cannot separate from phony; at prec 60 (floor 16, gate 14)
// every coefficient fits.  This is also the map on which the scalar
// RecognizeOverK misrecognized the LEADING coefficient at prec 60 (its
// reduced-precision LinearRelation was off by 3e-24), which is why every
// coefficient, the leading one included, now goes through the lattice fit.
//
// Q(sqrt -3) in test_degreebound_fallback.m is rejected by the reality check
// alone, since a real element of an imaginary quadratic field is rational.
// Over a real field every coefficient is real, so only the height gate on
// the degree-1 fits can reject Q: this is the test of that gate.  The
// passport size forces the ascent through degrees 2..6 as well, so phony
// relations at degrees 3 to 6 must be gated out after the quadratic field is
// found -- or rather, it is found first, at degree 2, and verified on all 19
// coefficients.
//
// The triple is as the LMFDB gives it: the LMFDB and this package share the
// convention sigma[3]*sigma[2]*sigma[1] = 1.
//
// PRECISION.  prec := 60 (see above).

AttachSpec("Code/spec");

S7 := Sym(7);
sigma := [S7 | [7,4,5,3,6,1,2], [4,6,7,3,2,1,5], [2,3,1,5,4,7,6]];
assert sigma[3]*sigma[2]*sigma[1] eq Id(S7);

Gamma := TriangleSubgroup(sigma);
assert Genus(Gamma) eq 2;
assert #PassportRepresentatives(sigma : Pointed := true) eq 7;

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
assert Discriminant(Integers(K)) eq 21;                   // K = Q(sqrt 21)
assert IsTotallyReal(K);

assert Genus(X) eq 2;
assert BelyiMapSanityCheck(sigma, X, phi);
assert Degree(phi) eq 7;

print "ALL TESTS PASSED";
quit;
