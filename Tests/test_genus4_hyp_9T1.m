// Genus 4 but HYPERELLIPTIC: checks that the dispatch does NOT take the
// quadric-and-cubic branch, and that the existing hyperelliptic path
// computes the map.  From BelyiDB:
//
//   belyi_db/9/9T1-[9,9,9]-9-9-9-g4.m
//
// Degree 9, the CYCLIC cover: monodromy C9, automorphism group C9.  Its
// canonical image is a rational normal cubic, which lies on three quadrics,
// so TriangleGenus4Test would report a 3-dimensional degree-2 kernel; the
// hyperelliptic test runs first and routes it away.
//
// DegreeBound := 1 IS THE POINT.  The passport has size 3, but its members
// (1,1,7), (1,7,1), (7,1,1) are related by the S_3 action on {0, 1, oo},
// not by Galois, so each is defined over Q.  With the default bound MakeK
// hunts for a cubic field that does not exist (the fallback in
// TriangleRecognizeAlgebraicCoefficients would then find Q, more slowly).
//
// THE ANSWER, small enough to write down and checked here independently:
//
//     X   : y^2 = x^10 - 2x        over Q,  genus 4
//     phi = (y + x^5)/(2 x^5),     phi*(phi - 1) = -1/(2 x^9)

AttachSpec("Code/spec");

S9 := Sym(9);
sigma := [S9 | [2,3,4,5,6,7,8,9,1], [2,3,4,5,6,7,8,9,1], [8,9,1,2,3,4,5,6,7]];

assert &*Reverse(sigma) eq Id(S9);
assert Order(sub<S9 | sigma>) eq 9;
assert #Centralizer(S9, sub<S9 | sigma>) eq 9;         // Aut(phi) = C9

Gamma := TriangleSubgroup(sigma);
assert Genus(Gamma) eq 4;
assert #PassportRepresentatives(sigma : Pointed := true) eq 3;

cbin := GetEnv("POWSER_ARNOLDI_BIN");
if cbin eq "" then cbin := "powser_arnoldi"; end if;
retc := System(Sprintf("command -v %o > /dev/null 2>&1 || test -x %o", cbin, cbin));
powseral := (retc eq 0) select "CArnoldi" else "Arnoldi";
printf "PowserAl := %o\n", powseral;

t0 := Cputime();
X, phi, Gamma := BelyiMap(Gamma : prec := 40, DegreeBound := 1, PowserAl := powseral);
printf "BelyiMap took %o s\n", Cputime(t0);

assert Gamma`TriangleIsHyperelliptic;
assert not (assigned Gamma`TriangleIsGenus4Canonical and Gamma`TriangleIsGenus4Canonical);
assert Genus(X) eq 4;
assert Degree(BaseRing(X)) eq 1;
assert Degree(phi) eq 9;
assert BelyiMapSanityCheck(sigma, X, phi);

// the closed form, verified on its own
P<xp> := PolynomialRing(Rationals());
Xc := HyperellipticCurve(xp^10 - 2*xp);
FFc<xx, yy> := FunctionField(Xc);
phic := (yy + xx^5)/(2*xx^5);
assert Genus(Xc) eq 4;
assert Degree(phic) eq 9;
assert phic*(phic - 1) eq -1/(2*xx^9);
assert BelyiMapSanityCheck(sigma, Xc, phic);

print "ALL TESTS PASSED";
quit;
