// Basic end-to-end tests through the classical pipeline, verified exactly
// against the ramification data.
AttachSpec("Code/spec");

// README example: degree 4, genus 0
sigma := [Sym(4) | (1,2,3,4), (1,3,4,2), (1,3,4)];
X, phi := BelyiMap(sigma);
assert BelyiMapSanityCheck(sigma, X, phi);

// LMFDB 5T3-4.1_4.1_2.2.1-a: degree 5, genus 0, orbit size 2,
// defined over the quadratic field Q(i)
// (https://www.lmfdb.org/Belyi/5T3/4.1/4.1/2.2.1/a/)
sigma2 := [Sym(5) | (1,4,5,2), (2,3,5,4), (1,4)(2,3)];
X2, phi2 := BelyiMap(sigma2);
assert BelyiMapSanityCheck(sigma2, X2, phi2);
assert Degree(BaseRing(X2)) eq 2;

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
