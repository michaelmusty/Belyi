// End-to-end Belyi map computations through the CERTIFIED recognition path
// (ExactAl := "Certified" / MAKEK_RELFINDER_BIN), including a map NOT
// defined over QQ.  Requires the built Cext/makek_relfinder binary:
//
//   MAKEK_RELFINDER_BIN=$PWD/Cext/makek_relfinder magma -b Tests/test_certified_belyi.m

AttachSpec("MagmaPolred/spec");
AttachSpec("Code/spec");

assert GetEnv("MAKEK_RELFINDER_BIN") ne "";

// ---- 1: genus 0, hyperbolic, defined over QQ (LMFDB 5T4-5_3.1.1_3.1.1-a):
// exercises MakeKBatch (field recognition) and the batched RecognizeOverK
// through the genus-0 Newton pipeline.
sigma1 := [Sym(5) | (1,3,2,5,4), (1,2,3), (1,4,5)];
X1, phi1 := BelyiMap(sigma1 : prec := 40, ExactAl := "Certified");
assert BelyiMapSanityCheck(sigma1, X1, phi1);
assert Degree(BaseRing(X1)) eq 1;
print "test 1 ok: genus-0 over QQ via certified path";

// ---- 2: genus 0 hyperbolic, degree 6, base field QQ(sqrt 10)
// (LMFDB 6T15-5.1_4.2_3.1.1.1-a, orbit size 2): a map NOT defined over QQ;
// exercises the certified field recognition (MakeKBatch finds the quadratic
// field) and the batched certified RecognizeOverK over it.
S6 := Sym(6);
sigma2 := [S6 | S6![2,4,3,5,6,1], S6![3,6,1,2,4,5], S6![2,3,1,4,5,6]];
assert sigma2[3]*sigma2[2]*sigma2[1] eq Id(S6);
X2, phi2 := BelyiMap(sigma2 : prec := 60, ExactAl := "Certified");
assert BelyiMapSanityCheck(sigma2, X2, phi2);
K2 := BaseRing(X2);
assert Degree(K2) eq 2;
R<x> := PolynomialRing(Rationals());
assert IsIsomorphic(NumberField(R!DefiningPolynomial(K2)), NumberField(x^2 - 10));
print "test 2 ok: genus-0 over QQ(sqrt 10) via certified path";

// ---- 3: genus 0, degree 6, base field of degree 4
// (LMFDB 6T16-4.2_3.2.1_3.2.1-a, orbit size 4; suggested by SamSchiavone):
// certified recognition of a quartic field through the genus-0 pipeline.
// LMFDB base field: x^4 - 2x^3 - 3x^2 + 4x - 2.
sigma3 := [S6 | S6![4,6,1,5,3,2], S6![2,3,1,5,4,6], S6![2,6,4,3,5,1]];
assert sigma3[3]*sigma3[2]*sigma3[1] eq Id(S6);
X3, phi3 := BelyiMap(sigma3 : prec := 80, ExactAl := "Certified");
assert BelyiMapSanityCheck(sigma3, X3, phi3);
K3 := BaseRing(X3);
assert Degree(K3) eq 4;
assert IsIsomorphic(NumberField(R!DefiningPolynomial(K3)),
                    NumberField(x^4 - 2*x^3 - 3*x^2 + 4*x - 2));
print "test 3 ok: genus-0 over a quartic field via certified path";

print "ALL TESTS PASSED";
exit;
