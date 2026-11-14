// Genus 4, not hyperelliptic: the GENERIC case, from BelyiDB.
//
//   belyi_db/9/9T27-[9,9,9]-9-9-9-g4.m
//
// Degree 9, cycle types (9, 9, 9), monodromy of order 504 (PSL(2,8)),
// TRIVIAL automorphism group, passport size 6, field of definition Q.
//
// PRECISION.  prec := 80 passes with the default options (centred pivot,
// tuned representative; heights 7, 13, 13, 17 for quadric, cubic, A, B).
// prec := 60 FAILS, instructively: B has height 17 and the recognition
// over Q, which has no residual gate, accepts a wrong 16-digit value; the
// map then has the wrong degree and only BelyiMapSanityCheck catches it,
// slowly.  The reference computation in M23-recompute passed at 60 with
// the RREF-row representative, whose heights here are 3, 5, 12, 11 -- but
// that representative fails on 9T25, so the default is tuned (see
// genus4.m and Doc/genus4.md for the comparison).  Measured at prec 80:
//     Centred pivot,  Tuned     7, 13, 13, 17   <- the default; passes at 80
//     Centred pivot,  RREFRow   3,  5, 12, 11   passes at 60
//     LastNonzero,    Tuned    12, 21, 21, 21   fails at 60 and 80
//     LastNonzero,    RREFRow   4,  6, 14, 13
// The recognition gate is a filter; the ramification is the referee.
// This test is gated behind RUNSLOW: about six minutes on its own.
//
// DegreeBound := 1 is passed, since the map is known to be over Q; see
// test_genus4_nonhyp_9T25.m for the run that exercises the fallback.

AttachSpec("Code/spec");

S9 := Sym(9);
sigma := [S9 | [8,3,7,1,6,2,4,9,5], [5,3,6,2,8,7,1,9,4], [9,3,4,6,8,1,2,7,5]];

assert &*Reverse(sigma) eq Id(S9);
assert Order(sub<S9 | sigma>) eq 504;                  // PSL(2,8)
assert #Centralizer(S9, sub<S9 | sigma>) eq 1;         // Aut(phi) trivial

Gamma := TriangleSubgroup(sigma);
assert Genus(Gamma) eq 4;
assert #PassportRepresentatives(sigma : Pointed := true) eq 6;

cbin := GetEnv("POWSER_ARNOLDI_BIN");
if cbin eq "" then cbin := "powser_arnoldi"; end if;
retc := System(Sprintf("command -v %o > /dev/null 2>&1 || test -x %o", cbin, cbin));
powseral := (retc eq 0) select "CArnoldi" else "Arnoldi";
printf "PowserAl := %o\n", powseral;

t0 := Cputime();
X, phi, Gamma := BelyiMap(Gamma : prec := 80, DegreeBound := 1, PowserAl := powseral);
printf "BelyiMap took %o s\n", Cputime(t0);

assert Genus(X) eq 4;
assert assigned Gamma`TriangleIsGenus4Canonical and Gamma`TriangleIsGenus4Canonical;
assert not Gamma`TriangleIsHyperelliptic;
assert Gamma`TriangleGenus4FormDegree eq 3;
assert [Degree(f) : f in DefiningPolynomials(X)] eq [2, 3];
assert Degree(BaseRing(X)) eq 1;                          // over Q

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
