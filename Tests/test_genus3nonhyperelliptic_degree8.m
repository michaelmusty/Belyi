// Genus 3, not hyperelliptic, degree 8: two triples for ONE curve.
//
// This is the file that exercises what KMSV 5.27 cannot.  N = 8 gives
// d = Ceiling(13/4) = 4, so dim I_4 = Binomial(2,2) = 1 and the reduction
// modulo the ideal actually runs; and H^0(4H - phi^*(oo)) has dimension
// 4*4 - 8 - 2 = 6, so without the vanishing-order tuning there would be six
// different representatives of the same map to choose between.
//
// The second triple is the first with 0 and oo swapped.  That is an S_3
// action on the branch points, so it is the SAME curve with phi replaced by
// 1/phi -- but sigma_0 now has TWO cycles instead of one, which is the case
// a single power series at one point cannot see all of phi^*(0) for.  If the
// first triple passes and the second does not, the multi-cycle handling is
// what broke, and nothing else.
//
// ---------------------------------------------------------------------
// THE CURVE, derived rather than looked up (the LMFDB has no genus 3 Belyi
// maps: belyi_galmaps holds genus 0, 1 and 2 only).  With
// c = (1,2,3,4,5,6,7,8) generating C_8 acting regularly on 8 points,
//
//     sigma_0 = c,   sigma_1 = c^5,   sigma_oo = c^2,
//
// and c^2 * c^5 * c = c^8 = 1, which is the package's relation
// sigma_3*sigma_2*sigma_1 = 1 (Magma composes left to right).  Cycle types
// (8), (8), (4,4), so c_0 + c_1 + c_oo = 1 + 1 + 2 = 4 and
// g = (2 + N - 4)/2 = 3.
//
// A cyclic cover of P^1 branched over 0, 1, oo with local exponents (1, 5, 2)
// is y^8 = x(x-1)^5.  Its holomorphic differentials decompose under
// y -> zeta_8*y with dim_j = -1 + <j/8> + <5j/8> + <2j/8>, which is 1 for
// j = 3, 6, 7 and 0 otherwise -- total 3, confirming the genus.  The three
// canonical coordinates therefore carry DISTINCT C_8 weights 3, 6, 7, and the
// six degree-2 monomials carry weights 6, 1, 2, 4, 5, 6 mod 8.  Only the pair
// (w_3^2, w_7^2) shares a weight, so the only candidate invariant quadric is
// alpha*w_3^2 + beta*w_7^2, which would force w_3/w_7 to be constant -- and
// it is not, since those are different eigenvectors.  There is no quadric, so
// the canonical image is NOT a conic and the curve is NOT hyperelliptic.
// (The same computation for exponents (1,1,6), i.e. y^8 = x(x-1), gives
// weights 5, 6, 7 and the invariant quadric w_5*w_7 - w_6^2 -- and indeed
// y^8 = x^2 - x is v^2 = 4u^8 + 1 in disguise, hyperelliptic.  So the control
// genuinely discriminates.)
//
// The invariant quartics sit in weight 0: w_3^3*w_7, w_3*w_7^3, w_6^4, so the
// canonical model has the shape a*X^3*Z + b*X*Z^3 + c*Y^4 = 0, nonsingular
// for a, b, c nonzero.
//
// A GALOIS COVER.  The monodromy group has order 8 = the degree, so
// Aut(phi) = C_8: this is the most symmetric case available and will not
// exercise anything that depends on trivial automorphisms.
// Tests/test_genus3nonhyperelliptic_generic.m is the S_8 counterpart.
// ---------------------------------------------------------------------
AttachSpec("Code/spec");

S8 := Sym(8);
c := S8!(1,2,3,4,5,6,7,8);

// the power series basis dominates the runtime; use the external C solver
// when it is available, as Tests/test_carnoldi_belyi.m does
cbin := GetEnv("POWSER_ARNOLDI_BIN");
if cbin eq "" then cbin := "powser_arnoldi"; end if;
retc := System(Sprintf("command -v %o > /dev/null 2>&1 || test -x %o", cbin, cbin));
powseral := (retc eq 0) select "CArnoldi" else "Arnoldi";
printf "PowserAl := %o\n", powseral;

// DegreeBound := 1, so K = Q.  The default is the PASSPORT SIZE, and for a
// cyclic cover the passport members are related by the S_3 action on the
// branch points rather than by Galois -- they differ only in which exponent
// sits at 0, 1, oo -- so each is defined over Q and the default sends MakeK
// hunting for a field that does not exist.  Same trap as 9T1-[9,9,9].
for u in [<[S8 | c, c^5, c^2], "sigma_0 an 8-cycle">,
          <[S8 | c^2, c^5, c],  "sigma_0 with TWO cycles (0 and oo swapped)">] do
  sigma := u[1];
  printf "\n=== %o ===\n", u[2];

  // Magma composes permutations left to right, so sigma_0 sigma_1 sigma_oo = 1
  // is the REVERSED product here.
  assert &*Reverse(sigma) eq Id(S8);
  assert IsTransitive(sub<S8 | sigma>);
  assert #sub<S8 | sigma> eq 8;                 // cyclic, so defined over Q

  Gamma := TriangleSubgroup(sigma);
  assert Genus(Gamma) eq 3;

  t0 := Cputime();
  X, phi, Gamma := BelyiMap(Gamma : prec := 60, DegreeBound := 1, PowserAl := powseral);
  printf "BelyiMap took %o s\n", Cputime(t0);

  // the curve
  assert Genus(X) eq 3;
  assert IsNonsingular(X);
  assert assigned Gamma`TriangleIsGenus3NonHyperelliptic and Gamma`TriangleIsGenus3NonHyperelliptic;
  assert not Gamma`TriangleIsHyperelliptic;
  // the whole point of this file: d = 4, so dim I_4 = 1 and the reduction
  // modulo the ideal actually runs
  assert Gamma`TriangleGenus3NonHyperellipticDegree eq 4;
  assert Degree(BaseRing(X)) eq 1;              // K = Q

  // the referee
  assert BelyiMapSanityCheck(sigma, X, phi);
  assert Degree(phi) eq 8;

  // and explicitly, against the cycle type of the matching entry of the
  // triple.  BelyiMapSanityCheck aggregates; this says which fibre is which.
  for v in [<phi, sigma[1]>, <phi - 1, sigma[2]>, <1/phi, sigma[3]>] do
    D := Divisor(v[1]);
    zeros := [<Valuation(D, p), Degree(p)> : p in Support(D) | Valuation(D, p) gt 0];
    // an EMPTY support must FAIL rather than pass vacuously: a constant
    // function has neither zeros nor poles
    assert #zeros ge 1;
    // a place of residue degree f with valuation m contributes m repeated f
    // TIMES.  Using m*f instead turns 2^8 1^7 into [1,2,2,2,4,4,8] -- the
    // right total with the wrong partition -- and fails a correct map.
    parts := Sort(&cat[[z[1] : k in [1..z[2]]] : z in zeros]);
    cyc := Sort(&cat[[q[1] : k in [1..q[2]]] : q in CycleStructure(v[2])]);
    assert &+parts eq 8;
    assert parts eq cyc;
  end for;
end for;

print "ALL TESTS PASSED";
quit;
