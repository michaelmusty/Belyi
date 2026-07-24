// Unit tests for the genus-1 Abel-Jacobi evaluation machinery:
//
//   * TriangleCosetVertexToComplexPlane -- the exact coset-path evaluation
//     (walks the word of the coset representative chart by chart, as the
//     period computation does; KMSV section 3);
//   * TriangleDiscToComplexPlane -- the adaptive path integrator for
//     anonymous disc points;
//   * NewtonGetRamificationPoints -- the ramification points on the curve.
//
// Checks, on each example:
//   (1) the two evaluations agree modulo the period lattice at every
//       fundamental domain vertex (they share only the series data, so this
//       cross-validates both implementations and the periods);
//   (2) every ramification point returned satisfies the curve equation to
//       working accuracy (the original single-expansion evaluation left only
//       ~5 correct digits and fails this by many orders of magnitude).
//
// The second example, with signature (5,5,4), is the chart layout that broke
// the earlier midpoint-chaining implementation; it is kept as a regression.
AttachSpec("Code/spec");

prec := 40;

function CheckExample(sigma)
  Gamma := TriangleSubgroup(sigma);
  Gamma := NewtonGetNumericalData(Gamma : prec := prec);
  Gamma := NewtonGetRamificationPoints(Gamma);
  Sk := Gamma`TriangleNewtonSk;
  FD := Gamma`TriangleNewtonFD;
  CC := BaseRing(Parent(Sk[1][1]));
  RR := RealField(CC);
  d := Gamma`TriangleD;

  // lattice data for comparisons mod Lambda
  Lambda := Gamma`TrianglePeriodLattice;
  M := Matrix([[Re(l), Im(l)] : l in Lambda]);
  latres := function(z)  // distance from z to the nearest lattice point
    sol := Solution(M, Vector([Re(z), Im(z)]));
    return Abs(z - Round(sol[1])*Lambda[1] - Round(sol[2])*Lambda[2]);
  end function;

  // (1) coset-path vs adaptive evaluation, at every FD vertex of every coset
  eps_agree := RR!10^(-(3*prec) div 4);
  maxdisagree := RR!0;
  for ind := 1 to d do
    for slot := 1 to 3 do
      w1 := TriangleCosetVertexToComplexPlane(ind, slot, Gamma, Sk);
      w2 := TriangleDiscToComplexPlane(FD[4*(ind-1)+slot], Gamma, Sk);
      dis := latres(w1 - w2);
      if dis gt maxdisagree then maxdisagree := dis; end if;
    end for;
  end for;
  printf "max disagreement (mod Lambda) between coset-path and adaptive AJ: %o\n",
    RealField(6)!maxdisagree;
  assert maxdisagree lt eps_agree;

  // (2) ramification points satisfy the curve equation
  c4, c6 := Explode(Gamma`TriangleNumericalCurveCoefficients);
  eps_curve := RR!10^(-(prec div 2));
  maxres := RR!0;
  for pts in [Gamma`TriangleNewtonRamificationPoints0,
              Gamma`TriangleNewtonRamificationPoints1,
              Gamma`TriangleNewtonRamificationPointsoo] do
    for P in pts do
      f := P[1]^3 - 27*c4*P[1] - 54*c6;
      scale := Max(RR!1, Max(Abs(P[2])^2, Abs(f)));
      res := Abs(P[2]^2 - f)/scale;
      if res gt maxres then maxres := res; end if;
    end for;
  end for;
  printf "max relative curve residual of ramification points: %o\n",
    RealField(6)!maxres;
  assert maxres lt eps_curve;

  return true;
end function;

// LMFDB 4T5-4_4_3.1-a: degree 4, genus 1, hyperbolic (4,4,3)
S4 := Sym(4);
assert CheckExample([S4 | S4![2,3,4,1], S4![3,1,4,2], S4![3,2,4,1]]);

// signature (5,5,4), degree 6, genus 1: the chart layout that defeated the
// midpoint-chaining implementation (regression)
S6 := Sym(6);
assert CheckExample([S6 | (1,2,3,5,6), (1,4,2,6,3), (1,2,3,4)(5,6)]);

print "ALL TESTS PASSED";
quit;
