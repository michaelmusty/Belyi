// Basic end-to-end tests through the classical pipeline, verified exactly
// against the ramification data.
AttachSpec("Code/spec");

// README example: degree 4, genus 1
sigma := [Sym(4) | (1,2,3,4), (1,3,4,2), (1,3,4)];
X, phi := BelyiMap(sigma : prec := 30);
assert BelyiMapSanityCheck(sigma, X, phi);

// LMFDB 5T4-5_3.1.1_3.1.1-a: degree 5, genus 0, hyperbolic (orders (5,3,3)),
// monodromy A5, orbit size 1, defined over Q
// (https://www.lmfdb.org/Belyi/5T4/5/3.1.1/3.1.1/a/)
sigma2 := [Sym(5) | (1,3,2,5,4), (1,2,3), (1,4,5)];
X2, phi2 := BelyiMap(sigma2 : prec := 40);
assert BelyiMapSanityCheck(sigma2, X2, phi2);
assert Degree(BaseRing(X2)) eq 1;   // defined over Q

// LMFDB 6T1-6_6_3.3-a: degree 6, cyclic monodromy C6, genus 2,
// orbit size 1, defined over Q, curve y^2 = x^6 - 2
// (https://www.lmfdb.org/Belyi/6T1/6/6/3.3/a/)
sigma3 := [Sym(6) | (1,2,3,4,5,6), (1,2,3,4,5,6), (1,5,3)(2,6,4)];
X3, phi3 := BelyiMap(sigma3 : prec := 40);   // prec 40 suffices and keeps the test fast
assert BelyiMapSanityCheck(sigma3, X3, phi3);
assert Genus(X3) eq 2;
assert Degree(BaseRing(X3)) eq 1;   // defined over Q

print "ALL TESTS PASSED";
quit;
