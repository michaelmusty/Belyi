// The DegreeBound fallback of TriangleRecognizeAlgebraicCoefficients, on the
// g4 PR review's reproduction (Doc/SPEC-degreebound-fallback.md).
//
//   belyi_db/9/9T6-[9,9,9]-9-9-9-g4.m   with   DegreeBound := 4
//
// The map is defined over Q(sqrt(-3)) and the bound is forced ABOVE the field
// degree, so MakeK finds no quartic field and the fallback must find the
// quadratic one.  Before the fix it accepted Q on the first five coefficients
// (the curve's, which are rational) and died at the sanity check; the fix
// gates Q on EVERY coefficient being real and fitting at degree 1, which a
// map over an imaginary quadratic field fails at its first non-real
// coefficient, and then verifies the quadratic candidate on all of them.
//
// Beyond the review's assertions this also checks the exact field: degree 2
// with discriminant -3 times a square, so test_genus4_nonhyp_9T6.m and this
// test could not pass on a map from the other (9,9,9) passports over Q.
//
// PRECISION.  prec := 40, as in test_genus4_nonhyp_9T6.m.

AttachSpec("Code/spec");

S9 := Sym(9);
sigma := [S9 | [2,3,4,5,6,7,8,9,1], [2,9,7,5,3,1,8,6,4], [2,6,1,5,9,4,8,3,7]];
assert &*Reverse(sigma) eq Id(S9);

Gamma := TriangleSubgroup(sigma);
assert Genus(Gamma) eq 4;
assert #PassportRepresentatives(sigma : Pointed := true) eq 2;   // the bound below is forced past it

cbin := GetEnv("POWSER_ARNOLDI_BIN");
if cbin eq "" then cbin := "powser_arnoldi"; end if;
retc := System(Sprintf("command -v %o > /dev/null 2>&1 || test -x %o", cbin, cbin));
powseral := (retc eq 0) select "CArnoldi" else "Arnoldi";
printf "PowserAl := %o\n", powseral;

t0 := Cputime();
X, phi, Gamma := BelyiMap(Gamma : prec := 40, DegreeBound := 4, PowserAl := powseral);
printf "BelyiMap took %o s\n", Cputime(t0);

K := BaseRing(X);
assert Degree(K) eq 2;
disc := Discriminant(DefiningPolynomial(K));
assert IsSquare(-disc/3);                                 // K = Q(sqrt(-3))
assert Degree(Gamma`TriangleK) eq 2;

assert Genus(X) eq 4;
assert BelyiMapSanityCheck(sigma, X, phi);
assert Degree(phi) eq 9;

print "ALL TESTS PASSED";
quit;
