// Genus 3, not hyperelliptic: the GENERIC case, from BelyiDB.
//
//   belyi_db/9/9T27-[9,9,3]-9-9-333-g3.m
//
// Degree 9, cycle types (9, 9, 3^3), monodromy PSL(2,8) of order 504.
//
// It also exercises what KMSV 5.27 cannot.  N = 9 gives
// d = Ceiling((9+5)/4) = 4, so
//
//   #degree-4 monomials in 3 variables = 15
//   h^0(4H) on a plane quartic         = 4*4 - 3 + 1 = 14
//   dim I_4                            = 1     -- the ideal reduction runs
//   h^0(dH - phi^*(inf)) = 4d - N - 2  = 5     -- the dimension tuning runs
// where KMSV has d = 3, dim I_3 = 0 and nothing to reduce.
//
// PRECISION.  prec := 60 passes; prec := 40 FAILS, and instructively.  At 40
// the curve is already nearly right -- most coefficients agree with the
// prec-60 answer -- while the map comes back with ~100-digit numerators and
// denominators that collapse to 12 digits at 60.

AttachSpec("Code/spec");

S9 := Sym(9);
sigma := [S9 | [8,3,7,1,6,2,4,9,5], [9,4,8,1,6,7,2,5,3], [2,5,7,6,1,8,9,4,3]];

assert &*Reverse(sigma) eq Id(S9);
assert Order(sub<S9 | sigma>) eq 504;                  // PSL(2,8)
assert #Centralizer(S9, sub<S9 | sigma>) eq 1;         // Aut(phi) trivial

Gamma := TriangleSubgroup(sigma);
assert Genus(Gamma) eq 3;
assert #PassportRepresentatives(sigma : Pointed := true) eq 1;   // rigid

cbin := GetEnv("POWSER_ARNOLDI_BIN");
if cbin eq "" then cbin := "powser_arnoldi"; end if;
retc := System(Sprintf("command -v %o > /dev/null 2>&1 || test -x %o", cbin, cbin));
powseral := (retc eq 0) select "CArnoldi" else "Arnoldi";
printf "PowserAl := %o\n", powseral;

t0 := Cputime();
X, phi, Gamma := BelyiMap(Gamma : prec := 60, DegreeBound := 1, PowserAl := powseral);
printf "BelyiMap took %o s\n", Cputime(t0);

assert Genus(X) eq 3;
assert assigned Gamma`TriangleIsGenus3NonHyperelliptic and Gamma`TriangleIsGenus3NonHyperelliptic;
assert not Gamma`TriangleIsHyperelliptic;
assert Gamma`TriangleGenus3NonHyperellipticDegree eq 4;   // Ceiling((9+5)/4)
assert Degree(BaseRing(X)) eq 1;                          // rigid, so K = Q

assert BelyiMapSanityCheck(sigma, X, phi);
assert Degree(phi) eq 9;

// and explicitly, against the cycle type of the matching entry of the triple.
for v in [<phi, sigma[1]>, <phi - 1, sigma[2]>, <1/phi, sigma[3]>] do
  D := Divisor(v[1]);
  zeros := [<Valuation(D, p), Degree(p)> : p in Support(D) | Valuation(D, p) gt 0];
  // an EMPTY support must FAIL rather than pass vacuously
  assert #zeros ge 1;
  // a place of residue degree f with valuation m contributes m repeated f
  // TIMES.  The fibre over infinity here is 3^3, which may well be a single
  // degree-3 place; using m*f would read it as [9] and pass the total while
  // failing the partition.
  parts := Sort(&cat[[z[1] : k in [1..z[2]]] : z in zeros]);
  cyc := Sort(&cat[[q[1] : k in [1..q[2]]] : q in CycleStructure(v[2])]);
  assert &+parts eq 9;
  assert parts eq cyc;
end for;

print "ALL TESTS PASSED";
quit;
