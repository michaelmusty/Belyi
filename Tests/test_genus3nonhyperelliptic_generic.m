// Genus 3, not hyperelliptic, degree 8, GENERIC: full S_8 monodromy and
// trivial Aut(phi).
//
// Tests/test_genus3nonhyperelliptic_degree8.m is a Galois cover -- monodromy
// of order 8 = the degree, so Aut(phi) = C_8, the most symmetric case
// available.  A transitive automorphism group is exactly where normalization
// degeneracies hide, so it cannot stand in for a generic map.  This is the
// counterpart: one of the 1440 degree-8 genus-3 triples with cycle types
// (8, 8, 7.1), all of which have S_8 monodromy.
//
//     sigma_0  = (1,2,3,4,5,6,7,8)
//     sigma_1  = (1,7,5,3,8,6,4,2)
//     sigma_oo = (2,3,4,5,6,7,8)
//
// Same d = 4 and dim I_4 = 1 as the cyclic case.
//
// EXPLORATORY, and gated accordingly.  Unlike the cyclic case, whose curve
// and field of definition are derived in that file's header, NOTHING here is
// known in advance: not the field of definition, not the passport size, and
// not whether this particular curve is hyperelliptic (it is overwhelmingly
// likely not to be -- hyperelliptic is codimension 1 in M_3 -- but that is a
// probabilistic statement, not a proof).  So:
//
//   * DegreeBound is left at the default, which is the passport size.  With
//     1440 triples of this cycle type the Galois orbit may be large, and
//     MakeK is O(m) lattice reductions per candidate coefficient.
//   * prec := 60 is a guess.  If recognition fails uniformly rather than
//     gradually, that is what clustered heights straddling the certification
//     limit look like, NOT necessarily a bug -- measure the height
//     distribution before diagnosing anything.
//   * if the curve turns out to be hyperelliptic, the dispatcher takes the
//     hyperelliptic branch and the TriangleIsGenus3NonHyperelliptic assertion
//     below fails.  That is information, not a regression: swap in another of
//     the 1440.
AttachSpec("Code/spec");

S8 := Sym(8);
sigma := [S8 | (1,2,3,4,5,6,7,8), (1,7,5,3,8,6,4,2), (2,3,4,5,6,7,8)];

// Magma composes permutations left to right, so sigma_0 sigma_1 sigma_oo = 1
// is the REVERSED product here.
assert &*Reverse(sigma) eq Id(S8);
assert IsTransitive(sub<S8 | sigma>);
assert #sub<S8 | sigma> eq Factorial(8);          // full S_8, so Aut(phi) = 1
assert [CycleStructure(s) : s in sigma] eq
       [[<8,1>], [<8,1>], [<7,1>, <1,1>]];

Gamma := TriangleSubgroup(sigma);
assert Genus(Gamma) eq 3;

cbin := GetEnv("POWSER_ARNOLDI_BIN");
if cbin eq "" then cbin := "powser_arnoldi"; end if;
retc := System(Sprintf("command -v %o > /dev/null 2>&1 || test -x %o", cbin, cbin));
powseral := (retc eq 0) select "CArnoldi" else "Arnoldi";
printf "PowserAl := %o\n", powseral;

t0 := Cputime();
X, phi, Gamma := BelyiMap(Gamma : prec := 60, PowserAl := powseral);
printf "BelyiMap took %o s\n", Cputime(t0);

assert Genus(X) eq 3;
assert IsNonsingular(X);
assert assigned Gamma`TriangleIsGenus3NonHyperelliptic and Gamma`TriangleIsGenus3NonHyperelliptic;
assert not Gamma`TriangleIsHyperelliptic;
assert Gamma`TriangleGenus3NonHyperellipticDegree eq 4;

assert BelyiMapSanityCheck(sigma, X, phi);
assert Degree(phi) eq 8;

for v in [<phi, sigma[1]>, <phi - 1, sigma[2]>, <1/phi, sigma[3]>] do
  D := Divisor(v[1]);
  zeros := [<Valuation(D, p), Degree(p)> : p in Support(D) | Valuation(D, p) gt 0];
  assert #zeros ge 1;
  // a place of residue degree f with valuation m contributes m repeated f
  // TIMES, not m*f once
  parts := Sort(&cat[[z[1] : k in [1..z[2]]] : z in zeros]);
  cyc := Sort(&cat[[q[1] : k in [1..q[2]]] : q in CycleStructure(v[2])]);
  assert &+parts eq 8;
  assert parts eq cyc;
end for;

print "ALL TESTS PASSED";
quit;
