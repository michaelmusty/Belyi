// ================================================================================
// Numerical linear algebra on power series, shared by the canonical-model code
// ================================================================================
//
// These are the helpers that genus3nonhyperelliptic.m introduced and genus4.m
// imported, moved here (2026-11-11, SPEC-genus5plus.md §3a) so that petri.m and
// genus-general.m can use them too.  Everything is in MONOMIAL coordinates and
// every basis is an RREF: a K-rational subspace has a K-rational RREF basis,
// because the pivots are decided by which columns are independent, whereas an
// orthonormal (NumericalKernel / Gram-Schmidt) basis is a transcendental
// combination of the K-rational vectors and unrecognizable at any precision.
//
// Column counts are in STRIDED units: the local coordinate w is a uniformizer
// at the expansion point P only up to the order e of the stabilizer there, so
// every ratio of forms has w-exponents divisible by e and only every e-th
// coefficient carries information.
//
// These are plain functions, not intrinsics; callers import what they need:
//
//   import "serieskernel.m" : SeriesZeroify, SeriesRREF, SeriesColumnsAvailable,
//       SeriesKernel, SeriesConditionNullSpace, SeriesReduceModRREF,
//       SeriesLastNonzero, SeriesAffineCoordinates, SeriesNormalizedForms;

import "genuszero.m" : RemoveLeadingZeros;

// Zero out coefficients that are noise RELATIVE to the largest coefficient in
// the same list.  An absolute cut, or one keyed to prec - 30, degenerates at
// low precision: at prec = 30 the factor is 1 and every coefficient reads as
// zero.  Everything here is keyed to the 10^(-prec/2) noise floor instead.
SeriesZeroify := function(coeffs, prec);
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
SeriesRREF := function(rows, tol);
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
SeriesColumnsAvailable := function(series, minval, stride);
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
// unknowns, use SeriesConditionNullSpace below.
SeriesKernel := function(series, minval, stride, ncols, eps, CC);
  rows := [[Coefficient(h, minval + stride*n) : n in [0..ncols-1]] : h in series];
  // No column scaling here (removed 2026-11-12 after a day in service; see
  // Doc/adr-series-stage-echelonization.md §3).  Rows whose coefficients
  // grow like R^-n, from poles of affine coordinates f_i/f_g at the other
  // zeros of f_g, wreck the kernel; the fix is to build the rows from
  // products of the forms themselves, as petri.m does, not to read affine
  // series on a smaller circle.
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
// vanishing conditions on the monomials -- which is the one shape
// NumericalKernel is not set up for (it wants at least as many columns as
// rows).  Columns are normalized before and un-normalized after, for the same
// reason the rows are in SeriesKernel.
SeriesConditionNullSpace := function(cons, nmons, CC, prec);
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
  R, piv := SeriesRREF(M, mx*10^(-(prec div 2)));
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

// Reduce the vector v modulo the RREF rows Ibas with pivot columns Ipiv:
// zero out v on the pivot columns.  The result is the unique element of
// v + span(Ibas) vanishing there, so this is canonical given the RREF.
SeriesReduceModRREF := function(v, Ibas, Ipiv);
  u := v;
  for k in [1..#Ibas] do
    c := u[Ipiv[k]];
    if Abs(c) ne 0 then
      u := [u[m] - c*Ibas[k][m] : m in [1..#u]];
    end if;
  end for;
  return u;
end function;

// The last index at which the list is nonzero (0 if none).
SeriesLastNonzero := function(L);
  i := #L;
  while (i ge 1) and (L[i] eq 0) do
    i -:= 1;
  end while;
  return i;
end function;

// The affine coordinates x_i = f_i/f_g, i = 1..g-1, of the canonical patch
// f_g <> 0, as series in the SAME local coordinate as TrianglePhi, built
// exactly as hyperelliptic.m builds x_CC: each form is re-expanded in
// kappa*w, its leading zeros stripped and its leading coefficient made 1.
// g = #Sk.  (genus3nonhyperelliptic.m and genus4.m keep their own 3- and
// 4-variable versions; this one is for petri.m and genus-general.m.)
// The g normalized forms themselves, in the same local coordinate as
// TrianglePhi: each re-expanded in kappa*w, leading zeros stripped, leading
// coefficient 1.  The HOMOGENEOUS alternative to SeriesAffineCoordinates: a
// degree-d monomial f_1^(m_1) ... f_g^(m_g) in these is a product of
// holomorphic forms, convergent on the whole disc, whereas the affine
// x^m = f^m / f_g^d has poles at every other zero of f_g (2026-11-12,
// SPEC-genus5plus.md §3).  The two give the SAME coefficient vectors for
// every relation, since every affine row is the homogeneous row divided by
// the one series f_g^d.
SeriesNormalizedForms := function(Sk, kappa, eps);
  CCw := Parent(Sk[1][1]);
  w := CCw.1;
  fs := [];
  for i in [1..#Sk] do
    fi := Evaluate(Sk[i][1], kappa*w);
    fi := RemoveLeadingZeros(fi, eps);
    fi := fi/LeadingCoefficient(fi);
    Append(~fs, fi);
  end for;
  return fs;
end function;

SeriesAffineCoordinates := function(Sk, kappa, eps);
  CCw := Parent(Sk[1][1]);
  w := CCw.1;
  g := #Sk;
  fs := [];
  for i in [1..g] do
    fi := Evaluate(Sk[i][1], kappa*w);
    fi := RemoveLeadingZeros(fi, eps);
    fi := fi/LeadingCoefficient(fi);
    Append(~fs, fi);
  end for;
  return [fs[i]/fs[g] : i in [1..g-1]];
end function;
