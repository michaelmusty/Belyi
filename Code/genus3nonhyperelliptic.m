// ================================================================================
// Genus 3, non-hyperelliptic
// ================================================================================
//
// A non-hyperelliptic curve of genus 3 is canonically a smooth plane quartic:
// the canonical map is a closed embedding onto a quartic in P^2 whose
// homogeneous coordinates are the echelonized basis f_1, f_2, f_3 of
// S_2(Gamma).  We work throughout in the affine coordinates on the patch
// f_3 <> 0,
//
//     x = f_1/f_3,   y = f_2/f_3,
//
// matching Klug-Musty-Schiavone-Voight and matching what hyperelliptic.m
// already does (x_CC := f1/f2 there).  The canonical class is the hyperplane
// class H (deg K = 2g-2 = 4 = deg H), so a form of degree d restricts to a
// section of dH.
//
// THE MAP.  Write D_0 = phi^*(0) and D_inf = phi^*(infinity), both of degree
// N = deg phi, and let P be the expansion centre.  A pair (A, B) of degree-d
// forms with A + phi*B = 0 as SERIES at P is one with A + phi*B = 0 as
// functions -- a series at one point determines a function on an irreducible
// curve -- so div(A) - div(B) = div(phi), so div(B) >= D_inf and
// div(A) = div(B) - D_inf + D_0.  The pairs therefore correspond bijectively
// to B in H^0(dH - D_inf), with A = -phi*B.  Nothing about this needs to see
// where phi vanishes or has poles AWAY from P: the series identity carries it
// all.  In particular sigma_0 need not be an N-cycle.
//
// EXACTLY ONE SOLUTION.  H^0(dH - D_inf) has dimension 4d - N - 2 >= 3, and
// every element of it gives the SAME phi with wildly different heights, so a
// representative has to be chosen -- and on the genus-4 M23 map that choice
// produced coefficients of height ~408 and ~295 digits that neither LLL nor
// Gm-Reduce could shrink, while the map's own content was ~130.  Choosing
// better is not the fix; having nothing to choose is.  hyperelliptic.m gets
// there by decrementing MSSV's t until the kernel is 1-dimensional.  We get
// there by the same idea in the coordinates available here: additionally
// require
//
//     ord_P(B) >= j,
//
// which cuts the solution space to H^0(dH - D_inf - j*P) and so lets j tune
// the dimension one step at a time.  dim is non-increasing in j and drops by
// at most 1 per step (one linear condition), and is >= 3 at j = 0, so some j
// gives exactly 1 and a monotone walk finds it.  j = 4d - N - 3 is the value
// that gives dimension 1 whenever dH - D_inf - j*P is nonspecial, which is
// where the walk starts; the loop is what handles the special case, exactly
// as hyperelliptic.m's `while ... t := t - 1` does.
//
// WHY NOT L(m*P).  MSSV section 6.3 phrases this as phi_0 in L(t*P) and
// phi_inf = phi_0/phi in L((s+t)*P), and hyperelliptic.m implements it that
// way via RiemannRochBasisHyperellipticAnalytic.  That function can exist
// because the hyperelliptic model hands it x and y, global functions whose
// pole divisors are known a priori to sit at infinity; L(m*infinity) is then
// just the monomials in them of low enough pole order, plus a PolarPart
// subtraction to kill the second point at infinity.  A plane quartic has no
// such coordinates at a general P: "poles only at P" is a condition about the
// other three points where a line through P meets the curve, and the single
// power series at P carries no information about them.  Getting those points
// means root-finding on the plane model away from P -- possible, but a new
// and untested source of numerical fragility.  The vanishing-order tuning
// above buys the same three things (arbitrary sigma_0, a 1-dimensional
// kernel, no representative to choose) out of machinery that is already here.
//
// THE STRIDE.  The local coordinate w is a uniformizer at P only up to the
// order e of the stabilizer there, so every ratio of forms has w-exponents
// divisible by e and only every e-th coefficient carries information.  With
// s = the length of the cycle of sigma_0 containing the base point,
// ord_P(phi) = s and ord_w(phi) = a, so e = a div s -- the same e that
// hyperelliptic.m computes.  All column counts here are in strided units.
//
// THE TORUS.  The echelonized basis has distinct orders of vanishing
// s_i = ord_P(f_i) and leading coefficient 1, so the only remaining ambiguity
// in the model is the local coordinate w -> mu*w, under which
// X_i -> mu^(s_i) X_i.  A projective monomial of multidegree e has weight
// sum_i e_i s_i, and dehomogenizing
//
//     x^a y^b  =  f_1^a f_2^b f_3^(d-a-b) / f_3^d
//
// is a pure SHIFT of every weight in a degree-d group by -d*s_3; the
// coefficients themselves do not change.  We hand AFFINE data to
// TriangleRescaleCoefficients, which is what undoes the torus.  That matters
// for two reasons.  First, it needs a nonzero coefficient of weight zero
// whenever the Bezout exponents it computes do not sum to zero; projectively
// the weight-zero monomial is f_1^d, which is exactly the one absent from the
// KMSV quartic, while affinely it is the constant term.  Second, Xgcd is
// applied to the weights themselves and not to their differences, so the
// shift decides which Bezout combination -- hence which algebraic factor,
// hence the heights -- one lands on.
//
// LAMBDA'S GROUP.  TriangleRescaleCoefficients reads its rescaling factor
// from num cat denom ALONE and merely rescales the curve afterwards.  That is
// deliberate: lambda only has to track the torus, so it may be read from any
// group, but it MUST be read from one whose weight gcd is 1, since from a
// group of gcd > 1 the coefficients at offsets not divisible by the gcd need
// a root of lambda and leave K entirely.  The KMSV quartic is even in f_2, so
// all of its weights are even, while the map's are consecutive.
//
// K-RATIONALITY OF EVERY REPRESENTATIVE.  Every basis taken here is an RREF
// in monomial coordinates.  That is not a convenience: a K-rational subspace
// has a K-rational RREF basis, because the pivots are decided by which
// columns are independent, whereas NumericalKernel's orthonormal basis (and
// any Gram-Schmidt complement) is a TRANSCENDENTAL combination of the
// K-rational vectors and is unrecognizable at any precision.
//
// WHAT CERTIFIES THE ANSWER.  Everything here is heuristic except the solve
// residual, which is the statement that phi = -A/B on this curve to full
// precision.  The referee for the whole pipeline is BelyiMapSanityCheck,
// which compares Support(Divisor(phi)) and Support(Divisor(phi - 1)) against
// CycleStructure(sigma), and which runs downstream of all of it.  Note that
// stability across precisions is NOT a gate: a spurious lattice fit is
// reproducible, so it survives comparison across precisions untouched.

import "genuszero.m" : RemoveLeadingZeros;

// --------------------------------------------------------------------------
// local helpers
// --------------------------------------------------------------------------

// Zero out coefficients that are noise RELATIVE to the largest coefficient in
// the same list.  An absolute cut, or one keyed to prec - 30, degenerates at
// low precision: at prec = 30 the factor is 1 and every coefficient reads as
// zero.  Everything here is keyed to the 10^(-prec/2) noise floor instead.
G3NonHypZeroify := function(coeffs, prec);
  assert #coeffs gt 0;
  CC := Parent(coeffs[1]);
  m := Max([Abs(c) : c in coeffs]);
  tol := m*10^(-(prec div 2));
  out := [];
  for c in coeffs do
    if Abs(c) lt tol then
      Append(~out, CC!0);
    else
      Append(~out, c);
    end if;
  end for;
  return out;
end function;

// Reduced row echelon form IN MONOMIAL COORDINATES, with partial pivoting by
// largest modulus.  Returns the pivot rows only, and the pivot columns.
G3NonHypRREF := function(rows, tol);
  M := [[z : z in v] : v in rows];
  nr := #M;
  if nr eq 0 then
    return M, [];
  end if;
  nc := #M[1];
  piv := [];
  rr := 1;
  for c in [1..nc] do
    if rr gt nr then
      break;
    end if;
    best := rr;
    for i in [rr..nr] do
      if Abs(M[i][c]) gt Abs(M[best][c]) then
        best := i;
      end if;
    end for;
    if Abs(M[best][c]) le tol then
      continue;
    end if;
    tmp := M[rr];  M[rr] := M[best];  M[best] := tmp;
    dd := M[rr][c];
    M[rr] := [z/dd : z in M[rr]];
    for i in [1..nr] do
      if i eq rr then
        continue;
      end if;
      fq := M[i][c];
      if Abs(fq) ne 0 then
        M[i] := [M[i][j] - fq*M[rr][j] : j in [1..nc]];
      end if;
    end for;
    Append(~piv, c);
    rr +:= 1;
  end for;
  return M[1..rr-1], piv;
end function;

// The largest number of STRIDED coefficient columns
// minval, minval + stride, minval + 2*stride, ... that every series in the
// list actually knows.  An exact element (the constant 1, which is the
// weight-zero monomial) has infinite absolute precision and imposes no bound,
// so it is skipped rather than compared.
G3NonHypColumnsAvailable := function(series, minval, stride);
  aps := [];
  for h in series do
    ap := AbsolutePrecision(h);
    if Type(ap) eq RngIntElt then
      Append(~aps, ap);
    end if;
  end for;
  if #aps eq 0 then
    return 0;
  end if;
  return (Min(aps) - minval + stride - 1) div stride;
end function;

// The (left) numerical kernel of the matrix whose ROWS are the strided
// coefficient vectors of the given series, returned as a sequence of
// coefficient lists indexed by the series.  Rows are normalized to unit norm
// before the kernel and the kernel vectors are un-normalized afterwards:
// monomials of different weight differ by many orders of magnitude, and on an
// unnormalized matrix Epsilon means nothing.
//
// Use only where ncols >= #series; where the conditions are FEWER than the
// unknowns, use G3NonHypConditionNullSpace below.
G3NonHypSeriesKernel := function(series, minval, stride, ncols, eps, CC);
  rows := [[Coefficient(h, minval + stride*n) : n in [0..ncols-1]] : h in series];
  nrm := [];
  for r in rows do
    s := Sqrt(&+[Abs(z)^2 : z in r]);
    if s eq 0 then
      s := Parent(s)!1;   // an identically zero row: leave it alone
    end if;
    Append(~nrm, s);
  end for;
  M := Matrix([[rows[i][j]/(CC!nrm[i]) : j in [1..ncols]] : i in [1..#rows]]);
  ker := NumericalKernel(M : Epsilon := eps);
  // read the rows off the matrix directly rather than through
  // KSpaceWithBasis, which has nothing to build a space from when the kernel
  // is trivial -- and a trivial kernel is a case we report, not crash on
  out := [];
  for i in [1..Nrows(ker)] do
    Append(~out, [ker[i][j]/(CC!nrm[j]) : j in [1..#series]]);
  end for;
  return out;
end function;

// Null space of the conditions  sum_j c_j * cons[k][j] = 0,  computed by RREF
// with partial pivoting.  This is the case where the number of conditions is
// SMALLER than the number of unknowns -- for the map there are exactly N
// vanishing conditions on Binomial(d+2,2) monomials -- which is the one shape
// NumericalKernel is not set up for (it wants at least as many columns as
// rows).  Columns are normalized before and un-normalized after, for the same
// reason the rows are in G3NonHypSeriesKernel.
G3NonHypConditionNullSpace := function(cons, nmons, CC, prec);
  nconds := #cons;
  assert nconds gt 0;
  nrm := [];
  for j in [1..nmons] do
    s := Sqrt(&+[Abs(cons[k][j])^2 : k in [1..nconds]]);
    if s eq 0 then
      s := Parent(s)!1;
    end if;
    Append(~nrm, s);
  end for;
  M := [[cons[k][j]/(CC!nrm[j]) : j in [1..nmons]] : k in [1..nconds]];
  mx := Max([Max([Abs(z) : z in r]) : r in M]);
  R, piv := G3NonHypRREF(M, mx*10^(-(prec div 2)));
  basis := [];
  for f in [1..nmons] do
    if f in piv then
      continue;
    end if;
    v := [CC | 0 : j in [1..nmons]];
    v[f] := CC!1;
    for k in [1..#piv] do
      v[piv[k]] := -R[k][f];
    end for;
    Append(~basis, [v[j]/(CC!nrm[j]) : j in [1..nmons]]);
  end for;
  return basis;
end function;

// x = f_1/f_3 and y = f_2/f_3 as series in the SAME local coordinate as
// TrianglePhi, built exactly as hyperelliptic.m builds x_CC and y_CC.
G3NonHypCoordinateSeries := function(Sk, kappa, eps);
  CCw := Parent(Sk[1][1]);
  w := CCw.1;
  fs := [];
  for i in [1..3] do
    fi := Evaluate(Sk[i][1], kappa*w);
    fi := RemoveLeadingZeros(fi, eps);
    fi := fi/LeadingCoefficient(fi);
    Append(~fs, fi);
  end for;
  return fs[1]/fs[3], fs[2]/fs[3];
end function;

// --------------------------------------------------------------------------
// the monomial basis
// --------------------------------------------------------------------------

intrinsic Genus3NonHyperellipticMonomials(d::RngIntElt) -> SeqEnum
  {Exponent pairs [a,b] with a + b le d, in increasing total degree, and with
   the weight-zero monomial [0,0] LAST.

   TriangleGenus3NonHyperellipticNumericalCoefficients and
   TriangleMakeBelyiMap must agree on this ordering, which is why it lives in
   one place.  Which entry is last no longer decides anything -- the caller
   passes rescale_ind to TriangleRescaleCoefficients rather than relying on
   the final entry -- but [0,0] must be PRESENT and its coefficient nonzero
   somewhere in numerator or denominator, since that is the weight-zero
   coefficient lambda needs.  Affinely [0,0] is the unique monomial of weight
   zero, because s_1 < s_2 < s_3 makes x and y both of negative weight.}

  require d ge 0 : "d must be nonnegative";
  mons := [];
  for e in [1..d] do
    for a := e to 0 by -1 do
      Append(~mons, [a, e-a]);
    end for;
  end for;
  Append(~mons, [0,0]);
  return mons;
end intrinsic;

// --------------------------------------------------------------------------
// the curve
// --------------------------------------------------------------------------

intrinsic TriangleGenus3NonHyperellipticTest(Sk::SeqEnum, Gamma::GrpPSL2Tri) -> Any
  {Genus 3, non-hyperelliptic: find the canonical plane quartic.

   Input: Sk, an echelonized basis for the space of weight 2 modular forms,
          given as the output of PowerSeriesBasis;
          Gamma, a triangle subgroup of genus 3.
   Output: nonhyp_bool, true if exactly one quartic relation is found;
           curve_coeffs, the coefficients of that relation, indexed by
           Genus3NonHyperellipticMonomials(4);
           curve_vals, the valuations (that is, the affine weights) of the
           corresponding monomial series.

   A kernel of dimension other than 1 means the model is degenerate -- the
   curve is hyperelliptic, so that the canonical image is a conic and every
   multiple of it lies in the kernel, or the precision is too low -- and we
   return false rather than erroring, so that the caller can say so.}

  require Genus(Gamma) eq 3 :
      "TriangleGenus3NonHyperellipticTest is only implemented for genus 3";
  require #Sk eq 3 :
      "Sk should be an echelonized basis of S_2(Gamma), which has dimension 3 in genus 3";

  prec := Precision(BaseRing(Parent(Sk[1][1])));
  eps := 10^(-prec/2);   // NB rational exponent -> FldReElt; (prec div 2) gives
                         // FldRatElt, which NumericalKernel rejects
  CC := BaseRing(Parent(Sk[1][1]));
  Delta := ContainingTriangleGroup(Gamma);
  _, kappa := TrianglePhi(Delta);

  vprint Shimura : "Creating series for coordinate functions x = f1/f3 and y = f2/f3...";
  x_CC, y_CC := G3NonHypCoordinateSeries(Sk, kappa, eps);
  vx := Valuation(x_CC);
  vy := Valuation(y_CC);
  // s_1 < s_2 < s_3 for an echelonized basis, so both weights are negative
  // and [0,0] is the unique affine monomial of weight zero.  Everything
  // downstream (the rescaler's weight-zero coefficient, the normalization by
  // the final entry of each list) depends on that.
  require vx lt 0 and vy lt 0 :
      "expected ord(f1/f3) and ord(f2/f3) to be negative; is Sk echelonized with increasing valuations?";

  // the stride: the local coordinate w is a uniformizer at P only up to the
  // order e of the stabilizer there, so every RATIO of forms has w-exponents
  // divisible by e and only every e-th coefficient carries information.  This
  // is the same e as hyperelliptic.m's `e := a div #CycleDecomposition(sigma[1])[1]`.
  sigma := DefiningPermutation(Gamma);
  aa := DefiningABC(Gamma)[1];
  s0 := #CycleDecomposition(sigma[1])[1];
  e := aa div s0;
  require e*s0 eq aa :
      "the ramification index at the expansion point does not divide a";
  require (vx mod e eq 0) and (vy mod e eq 0) :
      "ord(f1/f3) or ord(f2/f3) is not divisible by the stabilizer order";

  vprint Shimura : "Computing plane quartic...";
  mons := Genus3NonHyperellipticMonomials(4);
  series := [x_CC^(m[1])*y_CC^(m[2]) : m in mons];
  // take the valuations from the SERIES, not from a formula for the s_i:
  // that is what hyperelliptic.m does and it is automatically right
  curve_vals := [Valuation(h) : h in series];
  assert curve_vals eq [mons[i][1]*vx + mons[i][2]*vy : i in [1..#mons]];

  minval := Min(curve_vals);
  navail := G3NonHypColumnsAvailable(series, minval, e);
  ncols := Min(navail, Max(4*#series, #series + 20));
  error if ncols lt #series + 5,
      Sprintf("not enough terms in the power series basis for the quartic: %o columns available, %o needed; raise prec",
              navail, #series + 5);

  vprintf Shimura : "\tForming matrix of series coefficients (%o rows, %o columns, stride %o)...\n", #series, ncols, e;
  vprintf Shimura : "\tComputing numerical kernel...\n";
  ker := G3NonHypSeriesKernel(series, minval, e, ncols, eps, CC);

  if #ker ne 1 then
    vprintf Shimura : "No plane quartic found: kernel has dimension %o, expected 1 (hyperelliptic, or precision too low).\n", #ker;
    Gamma`TriangleIsGenus3NonHyperelliptic := false;
    return false, _, _;
  end if;

  curve_coeffs := G3NonHypZeroify(ker[1], prec);
  // normalize by the last nonzero coefficient
  lc_ind := #curve_coeffs;
  while (lc_ind ge 1) and (curve_coeffs[lc_ind] eq 0) do
    lc_ind := lc_ind - 1;
  end while;
  error if lc_ind lt 1, "the quartic relation is numerically zero; raise prec";
  pivot := curve_coeffs[lc_ind];
  curve_coeffs := [c/pivot : c in curve_coeffs];
  curve_coeffs := G3NonHypZeroify(curve_coeffs, prec);

  vprintf Shimura : "Exactly one plane quartic relation found!\n";
  vprintf Shimura : "curve_coeffs = %o\n", curve_coeffs;
  vprintf Shimura : "curve_vals = %o\n", curve_vals;
  Gamma`TriangleIsGenus3NonHyperelliptic := true;
  return true, curve_coeffs, curve_vals;
end intrinsic;

// --------------------------------------------------------------------------
// the curve and the map
// --------------------------------------------------------------------------

intrinsic TriangleGenus3NonHyperellipticNumericalCoefficients(Sk::SeqEnum, Gamma::GrpPSL2Tri :
    curve_coeffs := [], curve_vals := []) -> Any
  {Numerical curve, numerator and denominator coefficients for a
   non-hyperelliptic genus 3 Belyi map; assigns them to Gamma.

   Input: Sk, an echelonized basis for the space of weight 2 modular forms;
          Gamma, a triangle subgroup of genus 3;
          curve_coeffs and curve_vals, optionally, as returned by
          TriangleGenus3NonHyperellipticTest, to avoid recomputing the quartic.
   Output: Gamma, followed by curve_coeffs, lc, num_coeffs, denom_coeffs,
           curve_vals, num_vals, denom_vals, matching
           TriangleHyperellipticNumericalCoefficients attribute for attribute.

   phi = -A/B with A and B forms of the same degree d, so that the common
   scalar of the pair cancels in the ratio.  The pair is found as the kernel
   of the series identity A + phi*B = 0, additionally requiring B to vanish to
   an order at P that is TUNED so that the kernel is exactly 1-dimensional --
   there is then no representative to choose, which is the whole point; see
   the header comment of this file.  sigma_0 may have any number of cycles.
   Coefficients of A and B are indexed by
   Genus3NonHyperellipticMonomials(d), those of the quartic by
   Genus3NonHyperellipticMonomials(4).}

  require Genus(Gamma) eq 3 :
      "TriangleGenus3NonHyperellipticNumericalCoefficients is only implemented for genus 3";
  require #Sk eq 3 :
      "Sk should be an echelonized basis of S_2(Gamma), which has dimension 3 in genus 3";

  prec := Precision(BaseRing(Parent(Sk[1][1])));
  eps := 10^(-prec/2);   // NB rational exponent -> FldReElt; (prec div 2) gives
                         // FldRatElt, which NumericalKernel rejects
  CC := BaseRing(Parent(Sk[1][1]));
  gg := Genus(Gamma);   // NOT `g`: a polynomial ring with a generator named g
                        // would silently rebind it
  if not assigned Gamma`TriangleNumericalPrecision then
    Gamma`TriangleNumericalPrecision := prec;
  end if;

  Delta := ContainingTriangleGroup(Gamma);
  phipser, kappa := TrianglePhi(Delta);
  x_CC, y_CC := G3NonHypCoordinateSeries(Sk, kappa, eps);

  // ------------------------------------------------------------------
  // 1. the curve
  // ------------------------------------------------------------------
  if #curve_coeffs eq 0 then
    nonhyp_bool, curve_coeffs, curve_vals := TriangleGenus3NonHyperellipticTest(Sk, Gamma);
    error if not nonhyp_bool,
        "no plane quartic found: the curve may be hyperelliptic, or the precision too low";
  else
    Gamma`TriangleIsGenus3NonHyperelliptic := true;
  end if;
  qmons := Genus3NonHyperellipticMonomials(4);
  error if #curve_coeffs ne #qmons,
      Sprintf("expected %o quartic coefficients (Genus3NonHyperellipticMonomials(4)), got %o",
              #qmons, #curve_coeffs);

  // ------------------------------------------------------------------
  // 2. the shape of the problem
  // ------------------------------------------------------------------
  // deg K = 2g - 2 = 4, so degree-d forms cut a class of degree 4d and the
  // space of maps is H^0(dH - D_inf), of degree 4d - N.
  // d = Ceiling((N+5)/4) is the least d making 4d - N > 2g - 2 = 4, where
  // Riemann-Roch forces h^0 = 4d - N - g + 1 >= 3.  The ideal in degree d is
  // the multiples of the quartic, of dimension Binomial(d-2, 2).
  sigma := DefiningPermutation(Gamma);
  N := Degree(Parent(sigma[1]));
  d := Ceiling((N+5)/4);
  dimI := Binomial(d-2, 2);

  // s is the length of the cycle of sigma_0 containing the base point -- NOT
  // the degree.  ord_P(phi) = s, and sigma_0 may have any number of cycles:
  // the series identity A + phi*B = 0 never needs to see the other zeros.
  aa := DefiningABC(Gamma)[1];
  s := #CycleDecomposition(sigma[1])[1];
  e := aa div s;
  error if e*s ne aa,
      Sprintf("the ramification index %o at the expansion point does not divide a = %o", s, aa);
  // phi is the hauptmodul of the containing triangle group, so ord_w(phi) = a
  // exactly, and ord_P(phi) = a/e = s.
  vphi := Valuation(phipser);
  error if vphi ne aa,
      Sprintf("ord_w(phi) = %o, expected a = %o; the expansion is not centred where phi vanishes", vphi, aa);

  vprintf Shimura : "Computing Belyi map: deg phi = %o, ord_P(phi) = %o, forms of degree %o, dim I_%o = %o, stride %o\n",
      N, s, d, d, dimI, e;

  // ------------------------------------------------------------------
  // 3. the degree-d monomial series, and phi times each of them
  // ------------------------------------------------------------------
  mons := Genus3NonHyperellipticMonomials(d);
  nd := #mons;
  serd := [x_CC^(m[1])*y_CC^(m[2]) : m in mons];
  map_vals := [Valuation(h) : h in serd];
  assert map_vals eq [mons[i][1]*Valuation(x_CC) + mons[i][2]*Valuation(y_CC) : i in [1..nd]];
  minval := Min(map_vals);
  error if exists{v : v in map_vals | v mod e ne 0},
      "a monomial valuation is not divisible by the stabilizer order";
  // coerce phi into the monomials' own ring, so that every product happens in
  // one place rather than relying on Magma to find a common overstructure for
  // a rational power series and a complex one of negative valuation
  phiCC := Parent(serd[1])!phipser;
  phiserd := [h*phiCC : h in serd];

  // ------------------------------------------------------------------
  // 4. I_d, read off numerically as the degree-d forms vanishing identically
  //    on the curve rather than reconstructed as multiples of the quartic
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
  Ibas := [];
  Ipiv := [];
  if dimI gt 0 then
    isc := Max([Max([Abs(z) : z in v]) : v in kI]);
    Ibas, Ipiv := G3NonHypRREF(kI, isc*10^(-(prec div 2)));
    error if #Ibas ne dimI,
        Sprintf("the RREF of I_%o has %o rows, expected %o; raise prec", d, #Ibas, dimI);
  end if;

  // ------------------------------------------------------------------
  // 5. the joint system, with the vanishing order at P tuned so that the
  //    solution space is exactly 1-dimensional -- so there is no
  //    representative to choose.  See the header comment.
  // ------------------------------------------------------------------
  navailJ := G3NonHypColumnsAvailable(serd cat phiserd, minval, e);
  // the joint system has up to 2*nd rows, so over-determine it by the same
  // factor the reference implementation used (about six columns per row)
  ncolsJ := Min(navailJ, Max(6*nd, 2*nd + 20));
  error if ncolsJ lt 2*nd + 5,
      Sprintf("not enough terms in the power series basis for the joint system: %o strided columns available, %o needed; raise prec",
              navailJ, 2*nd + 5);

  jvan := Max(0, 4*d - N - 3);
  Bvec := [CC | ];
  Avec := [CC | ];
  found := false;
  tries := 0;
  while not found do
    tries +:= 1;
    error if tries gt 4*d + 6,
        Sprintf("the vanishing order at P did not settle on a 1-dimensional solution space after %o tries; raise prec", tries);

    // a basis of the degree-d forms vanishing to order >= jvan at P.  The
    // conditions are strided coefficients of the affine series, so this is
    // jvan conditions on nd unknowns -- fewer conditions than unknowns, which
    // is why it goes through the RREF null space rather than NumericalKernel.
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
    // convention TriangleMakeBelyiMap already uses, and the same order as
    // hyperelliptic.m's `[f*phi : f in denombasis] cat numbasis`
    Wphi := [&+[Wbas[k][m]*phiserd[m] : m in [1..nd]] : k in [1..#Wbas]];
    rows := Wphi cat serd;
    nc := Min(ncolsJ, G3NonHypColumnsAvailable(rows, minval, e));
    error if nc lt #rows + 5,
        Sprintf("not enough terms for the joint system at vanishing order %o: %o strided columns, %o rows; raise prec",
                jvan, nc, #rows);
    ker := G3NonHypSeriesKernel(rows, minval, e, nc, eps, CC);

    // back to monomial coordinates, then reduce BOTH halves modulo I_d.  The
    // order is not optional: reducing after echelonizing gives a different
    // and far larger representative -- on the genus-4 M23 map that single
    // swap moved recognition from 1 of 11 coefficients to 8 of 8.  The
    // 2*dim I_d directions (i, 0) and (0, i) reduce to zero and drop out.
    red := [];
    for v0 in ker do
      mv := Max([Abs(z) : z in v0]);
      if mv eq 0 then
        continue;
      end if;
      v := [z/mv : z in v0];
      Bm := [&+[v[k]*Wbas[k][m] : k in [1..#Wbas]] : m in [1..nd]];
      Am := [v[#Wbas + m] : m in [1..nd]];
      for kk in [1..#Ibas] do
        cb := Bm[Ipiv[kk]];
        if Abs(cb) ne 0 then
          Bm := [Bm[m] - cb*Ibas[kk][m] : m in [1..nd]];
        end if;
        ca := Am[Ipiv[kk]];
        if Abs(ca) ne 0 then
          Am := [Am[m] - ca*Ibas[kk][m] : m in [1..nd]];
        end if;
      end for;
      Append(~red, Bm cat Am);
    end for;

    hrows := [];
    if #red gt 0 then
      rsc := Max([Max([Abs(z) : z in u]) : u in red]);
      // if everything reduced to noise the whole kernel was I_d + I_d, that
      // is, there is no honest solution at this vanishing order
      if rsc gt 10^(-(prec div 3)) then
        hrows := G3NonHypRREF(red, rsc*10^(-(prec div 2)));
      end if;
    end if;

    vprintf Shimura : "\tvanishing order %o at P: solution space has dimension %o\n", jvan, #hrows;
    if #hrows eq 1 then
      // RREF of a 1-dimensional space: the pivot is 1 by construction, so
      // there is no leading coefficient to divide out and nothing to pick
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
  // 6. THE CORRECTNESS CHECK.  This residual IS the assertion that
  //    phi = -A/B on this curve, to full precision.  An expansion centred
  //    where phi has POLES rather than zeros fails it by tens of orders of
  //    magnitude, not marginally.
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
  // 7. undo the torus.  Affine data, as explained at the top of this file.
  //    rescale_ind names, per list, the coefficient to normalize by; without
  //    it TriangleRescaleCoefficients uses the FINAL entry of each list,
  //    which here is the constant term and need not be nonzero.
  // ------------------------------------------------------------------
  LastNonzero := function(L);
    i := #L;
    while (i ge 1) and (L[i] eq 0) do
      i -:= 1;
    end while;
    return i;
  end function;
  rinds := [LastNonzero(curve_coeffs), LastNonzero(num_coeffs), LastNonzero(denom_coeffs)];
  error if rinds[1] lt 1, "the quartic is numerically zero; raise prec";
  error if rinds[2] lt 1, "the numerator A is numerically zero; raise prec";
  error if rinds[3] lt 1, "the denominator B is numerically zero; raise prec";

  lambda, curve_coeffs, lc, num_coeffs, denom_coeffs :=
      TriangleRescaleCoefficients(Gamma, [curve_coeffs, num_coeffs, denom_coeffs],
                                         [curve_vals, num_vals, denom_vals] :
                                  rescale_ind := rinds);

  // ------------------------------------------------------------------
  // 8. write numerical attributes, matching TriangleHyperellipticNumericalCoefficients
  // ------------------------------------------------------------------
  Gamma`TriangleNumericalCurveCoefficients := curve_coeffs;
  Gamma`TriangleNumericalBelyiMapLeadingCoefficient := lc;
  Gamma`TriangleNumericalBelyiMapNumeratorCoefficients := num_coeffs;
  Gamma`TriangleNumericalBelyiMapDenominatorCoefficients := denom_coeffs;
  Gamma`TriangleRescalingFactor := lambda;
  Gamma`TriangleGenus3NonHyperellipticDegree := d;
  vprintf Shimura : "...Belyi map found!\n";
  return Gamma, curve_coeffs, lc, num_coeffs, denom_coeffs, curve_vals, num_vals, denom_vals;

end intrinsic;
