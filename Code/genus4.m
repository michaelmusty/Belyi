// ================================================================================
// Genus 4, non-hyperelliptic
// ================================================================================
//
// A non-hyperelliptic curve of genus 4 is canonically the complete
// intersection of a UNIQUE quadric Q and a cubic C in P^3, the homogeneous
// coordinates being the echelonized basis f_1, f_2, f_3, f_4 of S_2(Gamma).
// We work throughout in the affine coordinates on the patch f_4 <> 0,
//
//     x = f_1/f_4,   y = f_2/f_4,   z = f_3/f_4,
//
// exactly as genus3nonhyperelliptic.m works on the patch f_3 <> 0 of P^2.
// The canonical class is the hyperplane class H (deg K = 2g-2 = 6 = deg H),
// so a form of degree d restricts to a section of dH.
//
// Everything in the header comment of genus3nonhyperelliptic.m applies here
// unchanged -- the map as the series identity A + phi*B = 0, the stride, the
// torus, lambda's group, K-rationality of RREF representatives, and what
// certifies the answer -- and is not repeated.  Four things are specific to
// genus 4.
//
// THE CUBIC IS DEFINED ONLY MODULO THE QUADRIC.  The degree-3 forms vanishing
// on the curve are Q*{x, y, z, 1} (4 dimensions) plus C (1), so the degree-3
// kernel is 5-dimensional and C must be separated from span(Q*{x,y,z,1}).
// That is done by EXACT linear algebra -- reduce the kernel modulo an RREF
// basis of the multiples of Q, both in monomial coordinates, then RREF what
// survives -- and NOT by orthogonal projection, which is a transcendental
// combination of the K-rational vectors and is unrecognizable at any
// precision.  In the M23 work that single change took the cubic from height
// 68, saturated, to height 17, stable.
//
// THE IDEAL IS NONZERO IN THE MAP'S DEGREE.  N = deg phi forces the form
// degree d to be the least with 6d - N > 6 (so that the class dK - D_inf is
// nonspecial), and dim I_d = Binom(d+1,3) + Binom(d,3) - Binom(d-2,3) is 5
// already at d = 3.  Both halves of every kernel vector are reduced modulo
// I_d BEFORE echelonizing.
//
// THE SOLUTION SPACE IS FORCED TO DIMENSION 1, not chosen from.  With
// D_inf = phi^*(oo), the pairs (A, B) are B in H^0(dH - D_inf), A = -phi*B,
// a space of dimension 6d - N - 3 >= 3 whose every element gives the SAME
// phi with wildly different heights.  The degree-9 reference scripts in
// M23-recompute took an RREF row of it and got away with that only because
// their heights are at most ~9; on the M23 map the RREF row had height ~408
// digits against intrinsic content ~130.  So, as genus3nonhyperelliptic.m
// does, we additionally require ord_P(B) >= j and walk j until the reduced,
// echelonized solution space has dimension exactly 1.  The RREF of a
// 1-dimensional space has pivot 1: nothing to normalize, no row to pick.
//
// THE CURVE HAS TWO GROUPS.  Q and C are each defined only up to their own
// scalar, so after TriangleRescaleCoefficients -- which divides the whole
// curve list by ONE pivot -- the cubic is divided by a pivot of its own.
// (The reference scripts give every group its own pivot for the same
// reason: the within-group ratios are what is K-rational.)
//
// Hyperelliptic detection is free here: a hyperelliptic genus-4 curve has
// canonical image a rational normal cubic, which lies on THREE quadrics, so a
// degree-2 kernel of dimension 3 is a diagnosis rather than a failure.  The
// dispatch in belyi_main.m runs TriangleHyperellipticTest first, so this
// file only ever sees the non-hyperelliptic case in practice, but it reports
// the diagnosis anyway.

import "genuszero.m" : RemoveLeadingZeros;
import "genus3nonhyperelliptic.m" : G3NonHypZeroify, G3NonHypRREF,
    G3NonHypColumnsAvailable, G3NonHypSeriesKernel, G3NonHypConditionNullSpace;

// --------------------------------------------------------------------------
// local helpers
// --------------------------------------------------------------------------

// x = f_1/f_4, y = f_2/f_4, z = f_3/f_4 as series in the SAME local
// coordinate as TrianglePhi, built exactly as hyperelliptic.m builds x_CC.
G4CoordinateSeries := function(Sk, kappa, eps);
  CCw := Parent(Sk[1][1]);
  w := CCw.1;
  fs := [];
  for i in [1..4] do
    fi := Evaluate(Sk[i][1], kappa*w);
    fi := RemoveLeadingZeros(fi, eps);
    fi := fi/LeadingCoefficient(fi);
    Append(~fs, fi);
  end for;
  return fs[1]/fs[4], fs[2]/fs[4], fs[3]/fs[4];
end function;

// the last index at which the list is nonzero (0 if none)
G4LastNonzero := function(L);
  i := #L;
  while (i ge 1) and (L[i] eq 0) do
    i -:= 1;
  end while;
  return i;
end function;

// reduce the vector v modulo the RREF rows Ibas with pivot columns Ipiv:
// zero out v on the pivot columns.  The result is the unique element of
// v + span(Ibas) vanishing there, so this is canonical given the RREF.
G4ReduceModRREF := function(v, Ibas, Ipiv);
  u := v;
  for k in [1..#Ibas] do
    c := u[Ipiv[k]];
    if Abs(c) ne 0 then
      u := [u[m] - c*Ibas[k][m] : m in [1..#u]];
    end if;
  end for;
  return u;
end function;

// --------------------------------------------------------------------------
// the monomial basis
// --------------------------------------------------------------------------

intrinsic Genus4Monomials(d::RngIntElt) -> SeqEnum
  {Exponent triples [a,b,c] with a + b + c le d, in increasing total degree,
   and with the weight-zero monomial [0,0,0] LAST.

   TriangleGenus4Test, TriangleGenus4NumericalCoefficients and
   TriangleMakeBelyiMap must agree on this ordering, which is why it lives in
   one place.  [0,0,0] must be PRESENT, and its coefficient nonzero somewhere
   in numerator or denominator, since that is the weight-zero coefficient
   TriangleRescaleCoefficients needs.  Affinely [0,0,0] is the unique
   monomial of weight zero, because s_1 < s_2 < s_3 < s_4 makes x, y and z
   all of negative weight.}

  require d ge 0 : "d must be nonnegative";
  mons := [];
  for e in [1..d] do
    for a := e to 0 by -1 do
      for b := e-a to 0 by -1 do
        Append(~mons, [a, b, e-a-b]);
      end for;
    end for;
  end for;
  Append(~mons, [0,0,0]);
  return mons;
end intrinsic;

intrinsic Genus4IdealDimension(d::RngIntElt) -> RngIntElt
  {The dimension of the degree-d part of the ideal of a quadric meeting a
   cubic in P^3: Binomial(d+1,3) + Binomial(d,3) - Binomial(d-2,3), the
   multiples of Q plus the multiples of C minus the overlap Q*C.}
  require d ge 0 : "d must be nonnegative";
  return Binomial(d+1,3) + Binomial(d,3) - Binomial(d-2,3);
end intrinsic;

// --------------------------------------------------------------------------
// the curve
// --------------------------------------------------------------------------

intrinsic TriangleGenus4Test(Sk::SeqEnum, Gamma::GrpPSL2Tri) -> Any
  {Genus 4, non-hyperelliptic: find the canonical quadric and cubic in P^3.

   Input: Sk, an echelonized basis for the space of weight 2 modular forms,
          given as the output of PowerSeriesBasis;
          Gamma, a triangle subgroup of genus 4.
   Output: g4_bool, true if exactly one quadric and, modulo it, exactly one
           cubic are found;
           curve_coeffs, the 10 quadric coefficients indexed by
           Genus4Monomials(2) followed by the 20 cubic coefficients indexed by
           Genus4Monomials(3);
           curve_vals, the valuations (the affine weights) of the
           corresponding monomial series, in the same order.

   A degree-2 kernel of dimension 3 means the curve is HYPERELLIPTIC -- the
   canonical image is a rational normal cubic, which lies on three quadrics
   -- and we return false with that diagnosis rather than erroring, so that
   the caller can route it to the hyperelliptic path.  Any other dimension
   than 1 is reported as a precision problem.}

  require Genus(Gamma) eq 4 :
      "TriangleGenus4Test is only implemented for genus 4";
  require #Sk eq 4 :
      "Sk should be an echelonized basis of S_2(Gamma), which has dimension 4 in genus 4";

  prec := Precision(BaseRing(Parent(Sk[1][1])));
  eps := 10^(-prec/2);   // NB rational exponent -> FldReElt; (prec div 2) gives
                         // FldRatElt, which NumericalKernel rejects
  CC := BaseRing(Parent(Sk[1][1]));
  Delta := ContainingTriangleGroup(Gamma);
  _, kappa := TrianglePhi(Delta);

  vprint Shimura : "Creating series for coordinate functions x = f1/f4, y = f2/f4, z = f3/f4...";
  x_CC, y_CC, z_CC := G4CoordinateSeries(Sk, kappa, eps);
  vx := Valuation(x_CC);
  vy := Valuation(y_CC);
  vz := Valuation(z_CC);
  // s_1 < s_2 < s_3 < s_4 for an echelonized basis, so all three weights are
  // negative and [0,0,0] is the unique affine monomial of weight zero
  require vx lt 0 and vy lt 0 and vz lt 0 :
      "expected ord(f1/f4), ord(f2/f4), ord(f3/f4) all negative; is Sk echelonized with increasing valuations?";

  // the stride, exactly as in genus3nonhyperelliptic.m
  sigma := DefiningPermutation(Gamma);
  aa := DefiningABC(Gamma)[1];
  s0 := #CycleDecomposition(sigma[1])[1];
  e := aa div s0;
  require e*s0 eq aa :
      "the ramification index at the expansion point does not divide a";
  require (vx mod e eq 0) and (vy mod e eq 0) and (vz mod e eq 0) :
      "a coordinate valuation is not divisible by the stabilizer order";

  // ------------------------------------------------------------------
  // the quadric
  // ------------------------------------------------------------------
  vprint Shimura : "Computing the canonical quadric...";
  mons2 := Genus4Monomials(2);
  ser2 := [x_CC^(m[1])*y_CC^(m[2])*z_CC^(m[3]) : m in mons2];
  // valuations FROM THE SERIES, not from a formula
  vals2 := [Valuation(h) : h in ser2];
  assert vals2 eq [m[1]*vx + m[2]*vy + m[3]*vz : m in mons2];
  minval2 := Min(vals2);
  navail2 := G3NonHypColumnsAvailable(ser2, minval2, e);
  ncols2 := Min(navail2, Max(4*#ser2, #ser2 + 20));
  error if ncols2 lt #ser2 + 5,
      Sprintf("not enough terms in the power series basis for the quadric: %o columns available, %o needed; raise prec",
              navail2, #ser2 + 5);
  vprintf Shimura : "\tForming matrix of series coefficients (%o rows, %o columns, stride %o)...\n", #ser2, ncols2, e;
  k2 := G3NonHypSeriesKernel(ser2, minval2, e, ncols2, eps, CC);

  if #k2 eq 3 then
    vprintf Shimura : "The degree-2 kernel is 3-dimensional: the canonical image lies on three quadrics, so the curve is HYPERELLIPTIC (canonical model a rational normal cubic, not a quadric meeting a cubic).\n";
    Gamma`TriangleIsGenus4Canonical := false;
    return false, _, _;
  elif #k2 ne 1 then
    vprintf Shimura : "No canonical quadric found: kernel has dimension %o, expected 1 (precision too low?).\n", #k2;
    Gamma`TriangleIsGenus4Canonical := false;
    return false, _, _;
  end if;
  qcoeffs := G3NonHypZeroify(k2[1], prec);
  qind := G4LastNonzero(qcoeffs);
  error if qind lt 1, "the quadric relation is numerically zero; raise prec";
  qcoeffs := G3NonHypZeroify([c/qcoeffs[qind] : c in qcoeffs], prec);
  vprintf Shimura : "Exactly one quadric found!\n";

  // ------------------------------------------------------------------
  // the cubic, modulo the multiples of the quadric
  // ------------------------------------------------------------------
  vprint Shimura : "Computing the cubic...";
  mons3 := Genus4Monomials(3);
  ser3 := [x_CC^(m[1])*y_CC^(m[2])*z_CC^(m[3]) : m in mons3];
  vals3 := [Valuation(h) : h in ser3];
  assert vals3 eq [m[1]*vx + m[2]*vy + m[3]*vz : m in mons3];
  minval3 := Min(vals3);
  navail3 := G3NonHypColumnsAvailable(ser3, minval3, e);
  ncols3 := Min(navail3, Max(4*#ser3, #ser3 + 20));
  error if ncols3 lt #ser3 + 5,
      Sprintf("not enough terms in the power series basis for the cubic: %o columns available, %o needed; raise prec",
              navail3, #ser3 + 5);
  vprintf Shimura : "\tForming matrix of series coefficients (%o rows, %o columns, stride %o)...\n", #ser3, ncols3, e;
  k3 := G3NonHypSeriesKernel(ser3, minval3, e, ncols3, eps, CC);
  if #k3 ne 5 then
    vprintf Shimura : "The degree-3 kernel has dimension %o, expected 5 (four multiples of the quadric plus the cubic); raise prec.\n", #k3;
    Gamma`TriangleIsGenus4Canonical := false;
    return false, _, _;
  end if;

  // the multiples of Q in degree-3 monomial coordinates: Q*x, Q*y, Q*z, Q*1
  R3 := PolynomialRing(CC, 3);
  Mon3 := func<m | R3.1^(m[1])*R3.2^(m[2])*R3.3^(m[3])>;
  Qpol := &+[qcoeffs[i]*Mon3(mons2[i]) : i in [1..#mons2]];
  QL := [[MonomialCoefficient(f*Qpol, Mon3(m)) : m in mons3] : f in [R3.1, R3.2, R3.3, R3!1]];
  qsc := Max([Max([Abs(c) : c in r]) : r in QL]);
  QLr, qpiv := G3NonHypRREF(QL, qsc*10^(-(prec div 2)));
  error if #QLr ne 4,
      "the multiples of the quadric are numerically dependent; raise prec";

  // reduce every kernel vector modulo span(Q*{x,y,z,1}), drop the ones that
  // vanish, and RREF what is left: exactly one row, with pivot 1
  ksc := Max([Max([Abs(c) : c in v]) : v in k3]);
  red := [];
  for v in k3 do
    u := G4ReduceModRREF(v, QLr, qpiv);
    if Max([Abs(c) : c in u]) gt ksc*10^(-(prec div 3)) then
      Append(~red, u);
    end if;
  end for;
  error if #red eq 0, "every degree-3 kernel vector reduced to zero modulo the quadric; raise prec";
  rsc := Max([Max([Abs(c) : c in u]) : u in red]);
  Cr := G3NonHypRREF(red, rsc*10^(-(prec div 2)));
  error if #Cr ne 1,
      Sprintf("the cubic modulo the quadric has dimension %o, expected 1; raise prec", #Cr);
  ccoeffs := G3NonHypZeroify(Cr[1], prec);
  vprintf Shimura : "Exactly one cubic found modulo the quadric!\n";

  curve_coeffs := qcoeffs cat ccoeffs;
  curve_vals := vals2 cat vals3;
  vprintf Shimura : "curve_coeffs = %o\n", curve_coeffs;
  vprintf Shimura : "curve_vals = %o\n", curve_vals;
  Gamma`TriangleIsGenus4Canonical := true;
  return true, curve_coeffs, curve_vals;
end intrinsic;

// --------------------------------------------------------------------------
// the curve and the map
// --------------------------------------------------------------------------

intrinsic TriangleGenus4NumericalCoefficients(Sk::SeqEnum, Gamma::GrpPSL2Tri :
    curve_coeffs := [], curve_vals := [], Representative := "Tuned",
    Pivot := "Centred") -> Any
  {Numerical curve, numerator and denominator coefficients for a
   non-hyperelliptic genus 4 Belyi map; assigns them to Gamma.

   Input: Sk, an echelonized basis for the space of weight 2 modular forms;
          Gamma, a triangle subgroup of genus 4;
          curve_coeffs and curve_vals, optionally, as returned by
          TriangleGenus4Test, to avoid recomputing the quadric and cubic.
   Output: Gamma, followed by curve_coeffs, lc, num_coeffs, denom_coeffs,
           curve_vals, num_vals, denom_vals, matching
           TriangleGenus3NonHyperellipticNumericalCoefficients and
           TriangleHyperellipticNumericalCoefficients attribute for attribute.

   phi = -A/B with A and B forms of the same degree d, the least with
   6d - N > 6.  The pair is the kernel of the series identity A + phi*B = 0
   with B additionally required to vanish at P to an order TUNED so that the
   kernel, reduced modulo I_d, is exactly 1-dimensional; see the header
   comment of this file.  Coefficients of A and B are indexed by
   Genus4Monomials(d); those of the curve by Genus4Monomials(2) followed by
   Genus4Monomials(3).

   Representative := "Tuned" (the default) is the construction above, the
   same as in genus 3.  Representative := "RREFRow" imposes no vanishing at
   P, reduces the whole (6d - N - 3)-dimensional solution space modulo I_d,
   RREFs it in monomial coordinates and takes the first row whose B-part
   survives -- the method of the degree-9 reference scripts.  Neither rule
   picks a SMALL element of that space (both pick a corner of it decided by
   something unrelated to height), and which corner is smaller varies by
   passport; the default is the one with the smaller worst case.  Measured
   with the centred pivot, every map verified by BelyiMapSanityCheck,
   height = most digits in any numerator or denominator (Doc/genus4.md):

       9T25  prec 40   tuned  9, passes      RREF row 23, fails (at 60 too)
       9T6   prec 40   tuned  1, passes      RREF row not run
       9T27  prec 60   tuned 17, fails       RREF row 12, passes
       9T27  prec 80   tuned 17, passes      RREF row 12

   Pivot := "Centred" (the default) normalizes each group -- quadric, cubic,
   A, B -- by a coefficient whose weight is central in that group's range,
   which is what keeps the recognized heights small; Pivot := "LastNonzero"
   normalizes by the last nonzero entry (the constant term), as the genus-3
   code does, and is kept for comparison.}

  require Representative in ["Tuned", "RREFRow"] :
      "Representative should be \"Tuned\" or \"RREFRow\"";
  require Pivot in ["Centred", "LastNonzero"] :
      "Pivot should be \"Centred\" or \"LastNonzero\"";

  require Genus(Gamma) eq 4 :
      "TriangleGenus4NumericalCoefficients is only implemented for genus 4";
  require #Sk eq 4 :
      "Sk should be an echelonized basis of S_2(Gamma), which has dimension 4 in genus 4";

  prec := Precision(BaseRing(Parent(Sk[1][1])));
  eps := 10^(-prec/2);
  CC := BaseRing(Parent(Sk[1][1]));
  gg := Genus(Gamma);   // NOT `g`: a polynomial ring with a generator named g
                        // would silently rebind it
  if not assigned Gamma`TriangleNumericalPrecision then
    Gamma`TriangleNumericalPrecision := prec;
  end if;

  Delta := ContainingTriangleGroup(Gamma);
  phipser, kappa := TrianglePhi(Delta);
  x_CC, y_CC, z_CC := G4CoordinateSeries(Sk, kappa, eps);

  // ------------------------------------------------------------------
  // 1. the curve
  // ------------------------------------------------------------------
  if #curve_coeffs eq 0 then
    g4_bool, curve_coeffs, curve_vals := TriangleGenus4Test(Sk, Gamma);
    error if not g4_bool,
        "no quadric-and-cubic model found: the curve may be hyperelliptic, or the precision too low";
  else
    Gamma`TriangleIsGenus4Canonical := true;
  end if;
  mons2 := Genus4Monomials(2);
  mons3 := Genus4Monomials(3);
  nq := #mons2;
  nc3 := #mons3;
  error if #curve_coeffs ne nq + nc3,
      Sprintf("expected %o curve coefficients (Genus4Monomials(2) cat Genus4Monomials(3)), got %o",
              nq + nc3, #curve_coeffs);

  // ------------------------------------------------------------------
  // 2. the shape of the problem
  // ------------------------------------------------------------------
  // deg K = 2g - 2 = 6, so degree-d forms cut a class of degree 6d and the
  // space of maps is H^0(dH - D_inf), of degree 6d - N.  d is the least
  // making that exceed 2g - 2 = 6, where Riemann-Roch forces
  // h^0 = 6d - N - g + 1 = 6d - N - 3 >= 3.  Below that the class need not
  // be effective at all, which is what d = 4 showed for M23.
  sigma := DefiningPermutation(Gamma);
  N := Degree(Parent(sigma[1]));
  d := 1;
  while 6*d - N le 2*gg - 2 do
    d +:= 1;
  end while;
  dimI := Genus4IdealDimension(d);
  honest := 6*d - N - gg + 1;

  aa := DefiningABC(Gamma)[1];
  s := #CycleDecomposition(sigma[1])[1];
  e := aa div s;
  error if e*s ne aa,
      Sprintf("the ramification index %o at the expansion point does not divide a = %o", s, aa);
  vphi := Valuation(phipser);
  error if vphi ne aa,
      Sprintf("ord_w(phi) = %o, expected a = %o; the expansion is not centred where phi vanishes", vphi, aa);

  vprintf Shimura : "Computing Belyi map: deg phi = %o, ord_P(phi) = %o, forms of degree %o, dim I_%o = %o, honest dimension %o, stride %o\n",
      N, s, d, d, dimI, honest, e;

  // ------------------------------------------------------------------
  // 3. the degree-d monomial series, and phi times each of them
  // ------------------------------------------------------------------
  mons := Genus4Monomials(d);
  nd := #mons;
  serd := [x_CC^(m[1])*y_CC^(m[2])*z_CC^(m[3]) : m in mons];
  map_vals := [Valuation(h) : h in serd];
  assert map_vals eq [m[1]*Valuation(x_CC) + m[2]*Valuation(y_CC) + m[3]*Valuation(z_CC) : m in mons];
  minval := Min(map_vals);
  error if exists{v : v in map_vals | v mod e ne 0},
      "a monomial valuation is not divisible by the stabilizer order";
  phiCC := Parent(serd[1])!phipser;
  phiserd := [h*phiCC : h in serd];

  // ------------------------------------------------------------------
  // 4. I_d, read off numerically as the degree-d forms vanishing on the curve
  // ------------------------------------------------------------------
  navail := G3NonHypColumnsAvailable(serd, minval, e);
  ncolsI := Min(navail, Max(4*nd, nd + 20));
  error if ncolsI lt nd + 5,
      Sprintf("not enough terms in the power series basis for the map: %o strided columns available, %o needed; raise prec",
              navail, nd + 5);
  vprintf Shimura : "\tComputing I_%o...\n", d;
  kI := G3NonHypSeriesKernel(serd, minval, e, ncolsI, eps, CC);
  error if #kI ne dimI,
      Sprintf("dim I_%o came out %o, expected %o; raise prec", d, #kI, dimI);
  isc := Max([Max([Abs(c) : c in v]) : v in kI]);
  Ibas, Ipiv := G3NonHypRREF(kI, isc*10^(-(prec div 2)));
  error if #Ibas ne dimI,
      Sprintf("the RREF of I_%o has %o rows, expected %o; raise prec", d, #Ibas, dimI);

  // ------------------------------------------------------------------
  // 5. the joint system, with the vanishing order at P tuned so that the
  //    solution space is exactly 1-dimensional
  // ------------------------------------------------------------------
  navailJ := G3NonHypColumnsAvailable(serd cat phiserd, minval, e);
  ncolsJ := Min(navailJ, Max(6*nd, 2*nd + 20));
  error if ncolsJ lt 2*nd + 5,
      Sprintf("not enough terms in the power series basis for the joint system: %o strided columns available, %o needed; raise prec",
              navailJ, 2*nd + 5);

  // honest - 1 is the vanishing order giving dimension 1 whenever
  // dK - D_inf - j*P is nonspecial; the walk handles the special case.
  // The RREF-row method imposes no vanishing at all.
  tuned := Representative eq "Tuned";
  jvan := tuned select Max(0, honest - 1) else 0;
  Bvec := [CC | ];
  Avec := [CC | ];
  found := false;
  tries := 0;
  nc := 0;
  while not found do
    tries +:= 1;
    error if tries gt 6*d + 6,
        Sprintf("the vanishing order at P did not settle on a 1-dimensional solution space after %o tries; raise prec", tries);

    if jvan eq 0 then
      Wbas := [[CC | (m eq k select 1 else 0) : m in [1..nd]] : k in [1..nd]];
    else
      cons := [[Coefficient(serd[m], minval + e*k) : m in [1..nd]] : k in [0..jvan-1]];
      Wbas := G3NonHypConditionNullSpace(cons, nd, CC, prec);
    end if;
    error if #Wbas eq 0,
        Sprintf("no degree-%o form vanishes to order %o at P; raise prec", d, jvan);

    // rows: phi times each B-candidate FIRST, then the A-monomials, so that
    // the relation reads phi*B + A = 0, that is phi = -A/B -- the sign
    // convention TriangleMakeBelyiMap uses
    Wphi := [&+[Wbas[k][m]*phiserd[m] : m in [1..nd]] : k in [1..#Wbas]];
    rows := Wphi cat serd;
    nc := Min(ncolsJ, G3NonHypColumnsAvailable(rows, minval, e));
    error if nc lt #rows + 5,
        Sprintf("not enough terms for the joint system at vanishing order %o: %o strided columns, %o rows; raise prec",
                jvan, nc, #rows);
    ker := G3NonHypSeriesKernel(rows, minval, e, nc, eps, CC);

    // back to monomial coordinates, then reduce BOTH halves modulo I_d
    // BEFORE echelonizing; the 2*dim I_d directions (i, 0), (0, i) drop out
    red := [];
    for v0 in ker do
      mv := Max([Abs(c) : c in v0]);
      if mv eq 0 then
        continue;
      end if;
      v := [c/mv : c in v0];
      Bm := [&+[v[k]*Wbas[k][m] : k in [1..#Wbas]] : m in [1..nd]];
      Am := [v[#Wbas + m] : m in [1..nd]];
      Bm := G4ReduceModRREF(Bm, Ibas, Ipiv);
      Am := G4ReduceModRREF(Am, Ibas, Ipiv);
      Append(~red, Bm cat Am);
    end for;

    hrows := [];
    if #red gt 0 then
      rsc := Max([Max([Abs(c) : c in u]) : u in red]);
      if rsc gt 10^(-(prec div 3)) then
        hrows := G3NonHypRREF(red, rsc*10^(-(prec div 2)));
      end if;
    end if;

    vprintf Shimura : "\tvanishing order %o at P: solution space has dimension %o\n", jvan, #hrows;
    if not tuned then
      // the first RREF row whose B-part survives; the pivot of that row is
      // 1 but need not lie in the B-part, so B is not normalized here
      error if #hrows eq 0,
          "no (A,B) with phi = -A/B was found; raise prec";
      for r in hrows do
        if Max([Abs(r[m]) : m in [1..nd]]) gt 10^(-(prec div 3)) then
          found := true;
          Bvec := [r[m] : m in [1..nd]];
          Avec := [r[nd+m] : m in [1..nd]];
          break;
        end if;
      end for;
      error if not found, "every RREF row has a vanishing B-part; raise prec";
      vprintf Shimura : "\tRREF row taken from a %o-dimensional solution space\n", #hrows;
    elif #hrows eq 1 then
      found := true;
      Bvec := [hrows[1][m] : m in [1..nd]];
      Avec := [hrows[1][nd+m] : m in [1..nd]];
    elif #hrows eq 0 then
      error if jvan eq 0,
          "no (A,B) with phi = -A/B was found even with no vanishing imposed at P; raise prec";
      jvan -:= 1;
    else
      jvan +:= 1;
    end if;
  end while;

  // ------------------------------------------------------------------
  // 6. THE CORRECTNESS CHECK: phi = -A/B on this curve, to full precision
  // ------------------------------------------------------------------
  resnum := RealField(prec)!0;
  resden := RealField(prec)!0;
  for k in [0..nc-1] do
    n := minval + e*k;
    tot := &+[Bvec[m]*Coefficient(phiserd[m], n) : m in [1..nd]]
         + &+[Avec[m]*Coefficient(serd[m], n) : m in [1..nd]];
    sc := &+[Abs(Bvec[m]*Coefficient(phiserd[m], n)) : m in [1..nd]]
        + &+[Abs(Avec[m]*Coefficient(serd[m], n)) : m in [1..nd]];
    resnum := Max(resnum, Abs(tot));
    resden := Max(resden, sc);
  end for;
  error if resden eq 0, "the joint system is numerically zero; raise prec";
  relres := resnum/resden;
  vprintf Shimura : "\tphi = -A/B holds to relative residual %o\n", RealField(6)!relres;
  error if relres gt 10^(-(prec div 3)),
      Sprintf("phi = -A/B holds only to relative residual %o; raise prec, or check that the expansion is centred where phi vanishes",
              RealField(6)!relres);

  num_coeffs := G3NonHypZeroify(Avec, prec);
  denom_coeffs := G3NonHypZeroify(Bvec, prec);
  num_vals := map_vals;
  denom_vals := map_vals;
  vprintf Shimura : "unscaled numerator coeffs = %o\n", num_coeffs;
  vprintf Shimura : "unscaled denominator coeffs = %o\n", denom_coeffs;

  // ------------------------------------------------------------------
  // 7. undo the torus.  rescale_ind names, per list, the coefficient to
  //    normalize by.  For the curve that is a coefficient of the QUADRIC;
  //    the cubic, which carries its own scalar, is renormalized afterwards.
  // ------------------------------------------------------------------
  // The rescaler divides the whole curve list by ONE pivot, so hand it the
  // quadric alone as the curve: the cubic, which carries its own scalar, is
  // rescaled by lambda and normalized by its own pivot afterwards.  The
  // pivot choice itself is TriangleRescaleCoefficients' business.
  qpart := curve_coeffs[1..nq];
  qvals := curve_vals[1..nq];
  cpart := curve_coeffs[nq+1..nq+nc3];
  cvals := curve_vals[nq+1..nq+nc3];
  if Pivot eq "Centred" then
    rinds := "Centred";
  else
    rinds := [G4LastNonzero(qpart), G4LastNonzero(num_coeffs), G4LastNonzero(denom_coeffs)];
    error if rinds[1] lt 1, "the quadric is numerically zero; raise prec";
    error if rinds[2] lt 1, "the numerator A is numerically zero; raise prec";
    error if rinds[3] lt 1, "the denominator B is numerically zero; raise prec";
  end if;

  lambda, qpart, lc, num_coeffs, denom_coeffs :=
      TriangleRescaleCoefficients(Gamma, [qpart, num_coeffs, denom_coeffs],
                                         [qvals, num_vals, denom_vals] :
                                  rescale_ind := rinds);
  // the cubic, by hand: same lambda, its own pivot (centred, or last nonzero)
  cpart := [cpart[i]*lambda^(cvals[i]) : i in [1..nc3]];
  cpart := G3NonHypZeroify(cpart, prec);
  if Pivot eq "Centred" then
    cmx := Max([Abs(c) : c in cpart]);
    cnz := [i : i in [1..nc3] | Abs(cpart[i]) gt cmx*10^(-(prec div 2))];
    error if #cnz eq 0, "the cubic is numerically zero; raise prec";
    cmid := (Min([cvals[i] : i in cnz]) + Max([cvals[i] : i in cnz]))/2;
    cind := cnz[1];
    for i in cnz do
      if Abs(cvals[i] - cmid) lt Abs(cvals[cind] - cmid) then cind := i; end if;
    end for;
  else
    cind := G4LastNonzero(cpart);
    error if cind lt 1, "the cubic is numerically zero; raise prec";
  end if;
  cpart := [c/cpart[cind] : c in cpart];
  curve_coeffs := qpart cat cpart;

  // ------------------------------------------------------------------
  // 8. write numerical attributes
  // ------------------------------------------------------------------
  Gamma`TriangleNumericalCurveCoefficients := curve_coeffs;
  Gamma`TriangleNumericalBelyiMapLeadingCoefficient := lc;
  Gamma`TriangleNumericalBelyiMapNumeratorCoefficients := num_coeffs;
  Gamma`TriangleNumericalBelyiMapDenominatorCoefficients := denom_coeffs;
  Gamma`TriangleRescalingFactor := lambda;
  Gamma`TriangleGenus4FormDegree := d;
  vprintf Shimura : "...Belyi map found!\n";
  return Gamma, curve_coeffs, lc, num_coeffs, denom_coeffs, curve_vals, num_vals, denom_vals;
end intrinsic;
