import "genuszero.m" : RemoveLeadingZeros;
import "powser_iter_arfed.m" : FDReduce;

intrinsic TrianglePhi(GGamma::GrpPSL2 : p := 1, prec := 0, Bound := 100) -> Any
  {Computes solutions (Fp1 and Fp2) to the _2F_1 hypergeometric differential equation;
   Computes and returns psip as the ratio of these solutions scaled by kappa;
   Computes and returns series for phi (phipser) as the reversion of psip;
   p = 1 implies centered at z_a; p = 2 is centered at z_b; p = 3 is at z_c.}

  require p eq 1 : "p ne 1 is not implemented; instead, apply S_3 to the triple";

  Delta := ContainingTriangleGroup(GGamma);
  a,b,c := Explode(DefiningABC(Delta));

  DD := TriangleUnitDisc(Delta);
  if prec eq 0 then
    prec := DD`prec;
  end if;
  CC := ComplexField(prec);

  FDDeltaH := InternalTriangleFDH(Delta, UpperHalfPlane() : Precision := prec);
  z0 := ComplexValue(FDDeltaH[1]);
  z1 := ComplexValue(FDDeltaH[3]);

  // Solve the system to find A, B, C
  C := 1+1/a;
  B := 1/2*(1/a-1/b+1/c+1);
  A := 1/2*(1/a-1/b-1/c+1);

  A2 := A-C+1;
  B2 := B-C+1;
  C2 := 2-C;

  HypergeometricSeriesAt1 := function(A,B,C);
    return Gamma(CC ! C)*Gamma(CC ! (C-A-B))/
           (Gamma(CC ! (C-A))*Gamma(CC ! (C-B)));
  end function;

  Fp1_1 := HypergeometricSeriesAt1(A,B,C);
  Fp2_1 := HypergeometricSeriesAt1(A2,B2,C2);
  kappa := (z1-z0)/(z1-ComplexConjugate(z0))*Fp2_1/Fp1_1;

  R<t> := PowerSeriesRing(Rationals(),Bound);
  Rp<tp> := PuiseuxSeriesRing(Rationals(),Denominator(C)*Bound);

  Fp1 := (Rp ! HypergeometricSeries(A,B,C,t));
  Fp2 := tp^(1-C)*(Rp ! HypergeometricSeries(A2,B2,C2,t));
  psip := Fp1/Fp2;

  phipser := Reversion(psip);

  Rw<wk> := PowerSeriesRing(Rationals(), Bound*a);
  return Rw!phipser, kappa, psip;
end intrinsic;

intrinsic TriangleRamificationValues(Sk::SeqEnum[SeqEnum[RngSerPowElt]], Gamma::GrpPSL2 : NormalizeByTheta := true) -> Any
  {Input: Sk: A sequence of series expansions for modular forms of weight k of the triangle group Gamma
          Gamma: The triangle group
   Output: The ramification values for ratios of elements of Sk.
   Params: If "NormalizeByTheta", then each basis element fi of Sk is multiplied by Theta^si
           where si is the order of vanishing of fi at the center.}

  alphas := TriangleCosetRepresentatives(Gamma);

  Delta := ContainingTriangleGroup(Gamma);
  DD := TriangleUnitDisc(Gamma);
  prec := DD`prec;
  V := FundamentalDomain(Delta, DD);
  ws := [V[1],V[3],V[2]];

  if NormalizeByTheta then
    Theta := TriangleTheta(Sk, Gamma);
  else
    Theta := 1;
  end if;

  whichcoset := Gamma`TriangleWhichCoset;
  DDs := Gamma`TriangleDDs;

  CCw := Parent(Sk[1][1]);
  CC := BaseRing(CCw);
  eps := (RealField(CC)!10)^(-prec/2);

  rho := Max([Abs(z) : z in FundamentalDomain(Delta, DD)]);

  // Record degree of leading term for each modular form in basis
  // (only using first series expansion for each form)
  Skeval := Sk;
  ss := [];
  for i := 1 to #Skeval do
    si := [];
    for j := 1 to #Skeval[i] do
      f,s := RemoveLeadingZeros(Skeval[i][j],eps);
      Skeval[i][j] := f;
      Append(~si, s);
    end for;
    Append(~ss, si);
  end for;

  ssmin := [Min([ss[i][c] : i in [1..#ss]]) : c in [1..#ss[1]]];

  vals := [];
  for wi := 1 to 3 do
    w0 := ws[wi];
    wvals := [];
    for i := 1 to #alphas do
      wp, _, _, jind := FDReduce(alphas[i]*w0, Gamma);
      wjind := whichcoset[jind];
      wp_j := PlaneToDisc(DDs[wjind], DiscToPlane(UpperHalfPlane(), wp));
      assert Abs(wp_j) lt rho+eps;

      if Abs(wp_j) lt eps then
        wp_j_cc := CC!0;
        m := ssmin[wjind];
      else
        wp_j_cc := ComplexValue(wp_j);
        m := 0;
      end if;
      repeat
        vprint Shimura : wi, i, m, ComplexField(6)!ComplexValue(wp_j);
        val := [];
        for k := 1 to #Skeval do
//          Append(~val, Theta^m*Evaluate(Derivative(Skeval[k][wjind], m), ComplexValue(wp_j)));
          Append(~val, Theta^m*Evaluate(Skeval[k][wjind] div (CCw.1-wp_j_cc)^m, wp_j_cc));
        end for;
        m +:= 1;
      until &+[Abs(v) : v in val] gt eps;

      Append(~wvals, val);
    end for;
    Append(~vals, wvals);
  end for;

  return vals;
end intrinsic;
