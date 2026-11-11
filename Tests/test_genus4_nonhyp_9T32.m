// Genus 4, not hyperelliptic, the LARGEST passport within reach, from
// BelyiDB.  SLOW: run with RUNSLOW=1.
//
//   belyi_db/9/9T32-[9,9,9]-9-9-9-g4.m
//
// Degree 9, cycle types (9, 9, 9), TRIVIAL automorphism group, passport size
// 48, field of definition Q(sqrt(-3)).
//
// PRECISION.  prec := 100, as in the reference computation (belyi_9T32.m);
// the power series stage alone takes minutes, which is why this test is
// gated behind RUNSLOW.
//
// DegreeBound := 2 is passed: the passport has 48 members but the map is
// defined over a quadratic field, and hunting for a degree-48 field first
// would be pointless.

AttachSpec("Code/spec");

S9 := Sym(9);
sigma := [S9 | [3,4,5,7,2,9,6,1,8], [3,7,9,8,1,4,6,5,2], [4,8,5,9,1,2,6,3,7]];

assert &*Reverse(sigma) eq Id(S9);
assert #Centralizer(S9, sub<S9 | sigma>) eq 1;         // Aut(phi) trivial

Gamma := TriangleSubgroup(sigma);
assert Genus(Gamma) eq 4;
assert #PassportRepresentatives(sigma : Pointed := true) eq 48;

cbin := GetEnv("POWSER_ARNOLDI_BIN");
if cbin eq "" then cbin := "powser_arnoldi"; end if;
retc := System(Sprintf("command -v %o > /dev/null 2>&1 || test -x %o", cbin, cbin));
powseral := (retc eq 0) select "CArnoldi" else "Arnoldi";
printf "PowserAl := %o\n", powseral;

t0 := Cputime();
X, phi, Gamma := BelyiMap(Gamma : prec := 100, DegreeBound := 2, PowserAl := powseral);
printf "BelyiMap took %o s\n", Cputime(t0);

assert Genus(X) eq 4;
assert assigned Gamma`TriangleIsGenus4Canonical and Gamma`TriangleIsGenus4Canonical;
assert not Gamma`TriangleIsHyperelliptic;
assert Gamma`TriangleGenus4FormDegree eq 3;
assert [Degree(f) : f in DefiningPolynomials(X)] eq [2, 3];
K := BaseRing(X);
assert Degree(K) eq 2;
disc := Discriminant(DefiningPolynomial(K));
assert IsSquare(-disc/3);                                 // Q(sqrt(-3))

assert BelyiMapSanityCheck(sigma, X, phi);
assert Degree(phi) eq 9;

for v in [<phi, sigma[1]>, <phi - 1, sigma[2]>, <1/phi, sigma[3]>] do
  D := Divisor(v[1]);
  zeros := [<Valuation(D, p), Degree(p)> : p in Support(D) | Valuation(D, p) gt 0];
  assert #zeros ge 1;
  parts := Sort(&cat[[z[1] : k in [1..z[2]]] : z in zeros]);
  cyc := Sort(&cat[[q[1] : k in [1..q[2]]] : q in CycleStructure(v[2])]);
  assert &+parts eq 9;
  assert parts eq cyc;
end for;

print "ALL TESTS PASSED";
quit;
