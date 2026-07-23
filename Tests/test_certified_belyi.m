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

print "ALL TESTS PASSED";
exit;
