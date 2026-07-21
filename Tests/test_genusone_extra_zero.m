// Genus-1 tests exercising the "extra common zero" (special point) machinery
// in the Newton lift (MSSV Database paper, Section 5.2 and Remark 5.2.10).
//
// Background: phi = num/den with num in L(t*O), den in L((s+t)*O), where s is
// the ramification of the distinguished point O above 0 and t = d - s + 1.
// When sigma_0 is not a d-cycle the denominator generically needs the full
// pole order s+t = d+1 > d = deg(phi), so num and den share exactly one extra
// common zero P_s (it cancels in div(phi)), which Newton must track as a
// special point: 2 extra variables (x_s, y_s) and 3 extra equations.  When
// sigma_0 IS a d-cycle (0 totally ramified), s = d, t = 1 and there is no
// extra zero.  Intrinsically: the extra zero is absent iff the 0-fiber sums
// to O in the group law of E (the d-cycle case is the trivial instance), so
// s < d does NOT force the extra zero.  The predicate NeedsExtra in
// Code/genusone.m decides this from the numerical denominator coefficients;
// these tests pin down all three branches.
AttachSpec("Code/spec");

// ---- Control: sigma_0 a d-cycle, no extra zero ----------------------------
// LMFDB 4T5-4_4_3.1-a: degree 4, genus 1, hyperbolic (orders (4,4,3)),
// defined over Q, curve y^2 = x^3 + 47/768*x + 2359/55296.
// sigma_0 = (1,2,3,4) is a 4-cycle, so s = d = 4, t = 1: NeedsExtra false.
// (https://www.lmfdb.org/Belyi/4T5/4/4/3.1/a/)
S4 := Sym(4);
sigma := [S4 | S4![2,3,4,1], S4![3,1,4,2], S4![3,2,4,1]];
Gamma := TriangleSubgroup(sigma);
X, phi := BelyiMap(Gamma : prec := 40);
assert BelyiMapSanityCheck(sigma, X, phi);
assert Genus(X) eq 1;
assert Degree(BaseRing(X)) eq 1;   // defined over Q
assert assigned Gamma`TriangleNewtonNeedsExtra;
assert not Gamma`TriangleNewtonNeedsExtra;

// ---- Extra zero present: sigma_0 not a d-cycle ----------------------------
// LMFDB 6T12-5.1_5.1_3.3-a: degree 6, genus 1, hyperbolic (orders (5,5,3)),
// defined over Q, curve y^2 = x^3 + 7/6000*x + 41/540000.
// sigma_0 has cycle type 5.1, so s = 5, t = 2, and the 0-fiber is
// 5*O + Q with Q ne O.  The special point's class is
//   P_s ~ (s+t)*O - D_0, i.e. P_s = -(sum of the 0-fiber) = -Q ne O
// in the group law, so the extra zero is PROVABLY present for this triple
// (the degenerate case P_s = O cannot occur) and the Newton system needs
// the special point to be square.
// (https://www.lmfdb.org/Belyi/6T12/5.1/5.1/3.3/a/)
S6 := Sym(6);
sigma2 := [S6 | S6![2,3,4,6,5,1], S6![2,6,1,4,3,5], S6![2,3,1,5,6,4]];
Gamma2 := TriangleSubgroup(sigma2);
X2, phi2 := BelyiMap(Gamma2 : prec := 40);
assert BelyiMapSanityCheck(sigma2, X2, phi2);
assert Genus(X2) eq 1;
assert Degree(BaseRing(X2)) eq 1;   // defined over Q
assert assigned Gamma2`TriangleNewtonNeedsExtra;
assert Gamma2`TriangleNewtonNeedsExtra;

// ---- Degenerate: sigma_0 not a d-cycle, but STILL no extra zero -----------
// LMFDB 6T7-4.2_4.2_3.3-a: degree 6, genus 1, hyperbolic (orders (4,4,3)),
// defined over Q, curve y^2 = x^3 - 73/107163*x + 170/26040609.
// sigma_0 has cycle type 4.2, so s = 4 < d and generically the extra zero
// would be needed -- but this map factors through the x-line
// (phi = (x/1323 - 1/107163)/(x^3 - ...), no y in the map), so its 0-fiber
// is 4*O + 2*(r,0) with r = 1/81 and (r,0) 2-torsion: the fiber sums to O
// in the group law, both pole orders drop by one, and there is NO extra
// common zero.  NeedsExtra must be false even though s < d.  This pins down
// the data-driven predicate (and the trailing machine-zero stripping that
// feeds it) against the purely combinatorial criterion "s lt d", which
// would wrongly add the special point here (3 extra equations but only
// 2 extra variables: overdetermined system).
// (https://www.lmfdb.org/Belyi/6T7/4.2/4.2/3.3/a/)
S6b := Sym(6);
sigma3 := [S6b | S6b![5,1,6,2,4,3], S6b![3,5,4,6,2,1], S6b![5,3,4,2,6,1]];
Gamma3 := TriangleSubgroup(sigma3);
X3, phi3 := BelyiMap(Gamma3 : prec := 40);
assert BelyiMapSanityCheck(sigma3, X3, phi3);
assert Genus(X3) eq 1;
assert Degree(BaseRing(X3)) eq 1;   // defined over Q
assert assigned Gamma3`TriangleNewtonNeedsExtra;
assert not Gamma3`TriangleNewtonNeedsExtra;

print "ALL TESTS PASSED";
quit;
