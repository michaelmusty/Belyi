// Genus 4, not hyperelliptic: the FIRST genus-4 test, from BelyiDB.
//
//   belyi_db/9/9T25-[9,9,9]-9-9-9-g4.m
//
// Degree 9, cycle types (9, 9, 9), monodromy of order 324, TRIVIAL
// automorphism group, passport size 4, field of definition Q.
//
// The canonical model is a quadric meeting a cubic in P^3.  N = 9 gives the
// form degree d = 3, the least with 6d - N > 6, so
//
//   #monomials of degree <= 3 in 3 affine variables = 20
//   dim I_3 = 5     -- Q*{x,y,z,1} and C itself; the ideal reduction runs
//   h^0(3H - phi^*(oo)) = 6*3 - 9 - 3 = 6   -- the vanishing-order walk runs
//
// NO DegreeBound IS PASSED.  The passport has size 4 but the map is defined
// over Q, so MakeK finds no quartic field and TriangleRecognizeAlgebraicCoefficients
// falls back through smaller bounds to Q.  This test exercises that fallback;
// test_genus4_nonhyp_9T27.m passes the bound explicitly instead.
//
// PRECISION.  prec := 40 is what the reference computation in M23-recompute
// (belyi_9T25.m) used and passed at; heights come out at most 9.

AttachSpec("Code/spec");

S9 := Sym(9);
sigma := [S9 | [5,3,6,7,8,9,1,2,4], [4,3,6,7,8,9,2,1,5], [4,5,7,6,8,2,1,9,3]];

assert &*Reverse(sigma) eq Id(S9);
assert Order(sub<S9 | sigma>) eq 324;
assert #Centralizer(S9, sub<S9 | sigma>) eq 1;         // Aut(phi) trivial

Gamma := TriangleSubgroup(sigma);
assert Genus(Gamma) eq 4;
assert #PassportRepresentatives(sigma : Pointed := true) eq 4;

cbin := GetEnv("POWSER_ARNOLDI_BIN");
if cbin eq "" then cbin := "powser_arnoldi"; end if;
retc := System(Sprintf("command -v %o > /dev/null 2>&1 || test -x %o", cbin, cbin));
powseral := (retc eq 0) select "CArnoldi" else "Arnoldi";
printf "PowserAl := %o\n", powseral;

t0 := Cputime();
X, phi, Gamma := BelyiMap(Gamma : prec := 40, PowserAl := powseral);
printf "BelyiMap took %o s\n", Cputime(t0);

assert Genus(X) eq 4;
assert assigned Gamma`TriangleIsGenus4Canonical and Gamma`TriangleIsGenus4Canonical;
assert not Gamma`TriangleIsHyperelliptic;
assert Gamma`TriangleGenus4FormDegree eq 3;
assert Dimension(Ambient(X)) eq 3;                        // in P^3
assert [Degree(f) : f in DefiningPolynomials(X)] eq [2, 3];
assert Degree(BaseRing(X)) eq 1;                          // over Q

assert BelyiMapSanityCheck(sigma, X, phi);
assert Degree(phi) eq 9;

// and explicitly: all three fibres are totally ramified, [9,9,9], each a
// single rational point of multiplicity 9.
for v in [<phi, sigma[1]>, <phi - 1, sigma[2]>, <1/phi, sigma[3]>] do
  D := Divisor(v[1]);
  zeros := [<Valuation(D, p), Degree(p)> : p in Support(D) | Valuation(D, p) gt 0];
  // an EMPTY support must FAIL rather than pass vacuously
  assert #zeros ge 1;
  parts := Sort(&cat[[z[1] : k in [1..z[2]]] : z in zeros]);
  cyc := Sort(&cat[[q[1] : k in [1..q[2]]] : q in CycleStructure(v[2])]);
  assert &+parts eq 9;
  assert parts eq cyc;
  assert zeros eq [<9, 1>];
end for;

print "ALL TESTS PASSED";
quit;
