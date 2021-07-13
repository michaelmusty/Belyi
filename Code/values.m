import "genuszero.m" : RemoveLeadingZeros;
import "powser_iter_arfed.m" : FDReduce;

intrinsic TriangleRamificationValues(Sk::SeqEnum[SeqEnum[RngSerPowElt]], Gamma::GrpPSL2Tri : NormalizeByTheta := true) -> Any
  {Input: Sk: A sequence of series expansions for modular forms of weight k of the triangle group Gamma
          Gamma: The triangle group
   Output: The ramification values for ratios of elements of Sk.
   Params: If "NormalizeByTheta", then each basis element fi of Sk is multiplied by Theta^si
           where si is the order of vanishing of fi at the center.}

  alphas := CosetRepresentatives(Gamma);

  Delta := ContainingTriangleGroup(Gamma);
  DD := UnitDisc(Gamma);
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
