// Genus 4, not hyperelliptic, with a NONTRIVIAL automorphism group, from
// BelyiDB.
//
//   belyi_db/9/9T6-[9,9,9]-9-9-9-g4.m
//
// Degree 9, cycle types (9, 9, 9), monodromy of order 27, automorphism group
// of order 3, passport size 2, field of definition Q(sqrt(-3)).
//
// This is the test for the weight-gcd branch of TriangleRescaleCoefficients:
// the reference computation reports a weight step of 3, equal to the order of
// the automorphism group, so lambda^(1/3) is determined only up to a cube
// root of unity.  All weights are then divisible by 3 and the ambiguity
// never leaves K; the sanity check is what certifies that.
//
// PRECISION.  prec := 40, as in the reference computation (belyi_9T6.m).

AttachSpec("Code/spec");

S9 := Sym(9);
sigma := [S9 | [2,3,4,5,6,7,8,9,1], [2,9,7,5,3,1,8,6,4], [2,6,1,5,9,4,8,3,7]];

assert &*Reverse(sigma) eq Id(S9);
assert Order(sub<S9 | sigma>) eq 27;
assert #Centralizer(S9, sub<S9 | sigma>) eq 3;         // Aut(phi) of order 3

Gamma := TriangleSubgroup(sigma);
assert Genus(Gamma) eq 4;
assert #PassportRepresentatives(sigma : Pointed := true) eq 2;

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
assert [Degree(f) : f in DefiningPolynomials(X)] eq [2, 3];
K := BaseRing(X);
assert Degree(K) eq 2;
// K = Q(sqrt(-3)): the discriminant of the defining polynomial is -3 times a
// square, whatever generator MakeK happened to pick
disc := Discriminant(DefiningPolynomial(K));
assert IsSquare(-disc/3);

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
