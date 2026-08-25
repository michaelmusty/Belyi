// Genus 3, not hyperelliptic: KMSV Example 5.27 (Klug-Musty-Schiavone-Voight,
// LMS JCM 17 (2014), p. 50).  A rigid (7,7,7)-triple generating PSL_2(F_7),
// refined passport of genus 3, over K = Q(sqrt(-7)).  The canonical model is
// a smooth plane quartic, so this exercises Code/genus3nonhyperelliptic.m.
//
// SMOKE TEST ONLY.  N = 7 gives d = 3, hence dim I_3 = 0, so this case cannot
// exercise the ideal reduction; and its coefficients are small enough that
// almost any representative recognizes, so it cannot exercise the
// conditioning either.  Tests/test_genus3nonhyperelliptic_degree8.m is the
// case that does both.
//
// This asserts RAMIFICATION, not coefficients.  Any lambda built from
// coefficients is mu^(-1) times an algebraic number, so what is recovered is
// the paper's curve twisted by an algebraic diagonal alpha^(s_i); the printed
// quartic and the paper's points (0 : -+nu : 1) will NOT match literally and
// are not supposed to.  What the paper's [7,7,7] actually asserts, and what
// is invariant under the twist, is that each fibre is a single rational point
// of multiplicity 7.
AttachSpec("Code/spec");

S7 := Sym(7);
sigma := [S7 | (1,2,3,4,5,6,7), (1,6,2,5,7,3,4), (1,5,3,6,2,4,7)];

// Magma composes permutations left to right, so sigma_0 sigma_1 sigma_oo = 1
// is the REVERSED product here.
assert &*Reverse(sigma) eq Id(S7);
assert IsTransitive(sub<S7 | sigma>);

Gamma := TriangleSubgroup(sigma);
assert Genus(Gamma) eq 3;

// prec 60 is comfortable; the example is verified down to 30.  Do NOT let
// belyi_main.m pick the default prec := 30+5*(Genus+1)*d, which is 170 here
// and very slow -- the power series basis dominates and is superlinear in
// precision.
//
// DegreeBound := 2 is passed explicitly because the default is the PASSPORT
// SIZE, which is not the same as the degree of the field of definition: this
// triple is rigid, and MakeK short circuits to K = Q whenever it is handed
// m = 1, which would silently produce nonsense over Q instead of over
// K = Q(sqrt(-7)).
//
// The power series basis dominates the runtime, so use the external C solver
// when it is available -- as Tests/test_carnoldi_belyi.m does, and as the
// reference implementation did -- and fall back to the pure-Magma Arnoldi
// iteration otherwise, so that this test never skips.
cbin := GetEnv("POWSER_ARNOLDI_BIN");
if cbin eq "" then cbin := "powser_arnoldi"; end if;
retc := System(Sprintf("command -v %o > /dev/null 2>&1 || test -x %o", cbin, cbin));
powseral := (retc eq 0) select "CArnoldi" else "Arnoldi";
printf "PowserAl := %o\n", powseral;

t0 := Cputime();
X, phi, Gamma := BelyiMap(Gamma : prec := 60, DegreeBound := 2, PowserAl := powseral);
printf "BelyiMap took %o s\n", Cputime(t0);

// the curve: a smooth plane quartic of genus 3
assert Genus(X) eq 3;
assert IsNonsingular(X);
// and the dispatcher really did take the genus 3 non-hyperelliptic branch
// rather than the hyperelliptic one.  (A smooth plane quartic is never
// hyperelliptic, so this is what that fact is here to confirm; the attributes
// are cheaper and more direct than calling IsHyperelliptic on the curve.)
assert assigned Gamma`TriangleIsGenus3NonHyperelliptic and Gamma`TriangleIsGenus3NonHyperelliptic;
assert not Gamma`TriangleIsHyperelliptic;
assert Gamma`TriangleGenus3NonHyperellipticDegree eq 3;   // Ceiling((7+5)/4)

// the field of definition
K := BaseRing(X);
assert Degree(K) eq 2;
assert #Roots(PolynomialRing(K)![2, 1, 1]) gt 0;   // x^2 + x + 2, so Q(sqrt(-7))

// the referee
assert BelyiMapSanityCheck(sigma, X, phi);

// and explicitly, since BelyiMapSanityCheck aggregates: all three fibres
// totally ramified, [7,7,7]
assert Degree(phi) eq 7;
for f in [phi, phi - 1] do
  D := Divisor(f);
  S := Support(D);
  zeros := [<Valuation(D, p), Degree(p)> : p in S | Valuation(D, p) gt 0];
  poles := [<-Valuation(D, p), Degree(p)> : p in S | Valuation(D, p) lt 0];
  // an EMPTY support must FAIL rather than pass vacuously: a constant
  // function has neither zeros nor poles, and a draft of this check accepted
  // deg phi = 0 for exactly that reason
  assert #zeros eq 1 and #poles eq 1;
  assert zeros[1] eq <7, 1> and poles[1] eq <7, 1>;
end for;

print "ALL TESTS PASSED";
quit;
