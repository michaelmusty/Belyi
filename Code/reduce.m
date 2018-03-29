intrinsic TriangleReduceToFundamentalTriangle(Delta::GrpPSL2, w::SpcHydElt) -> GrpPSL2Elt, SpcHydElt
  {Reduces w to a point wp in the fundamental triangle, with the reducing element
   delta in Delta such that wp = delta*w.}

  require IsTriangleGroup(Delta) : "Delta must be a triangle group";

  prec := Parent(w)`prec;
  CC<I> := Parent(ComplexValue(w));
  RR := RealField(prec);
  HH := UpperHalfPlane();
  DD := Parent(w);
  pi := Pi(RR);

  a,b := Explode(DefiningABC(Delta));

  A := InternalTriangleSwapOriginMap(Delta : Precision := prec);

  delta := Id(Delta);
  deltaa := Delta.1;
  deltab := Delta.2;

  wp := w;

  iold := 0;
  jold := 0;
  wpold := wp;
  repeat
    alpha := Argument(wp);
    i := -Floor(a*alpha/(2*pi)+1/2);
    wp := deltaa^i*wp;
    delta := deltaa^i*delta;
    wpp := -(A*wp);

    beta := Argument(wpp);
    j := -Floor(b*beta/(2*pi)+1/2);

    if i eq 0 and iold eq 0 and j eq -jold then
      // Flipping between representatives on the boundary, just pick one.
      j := 0;
    else
      iold := i;
      jold := j;
    end if;
    wp := deltab^j*wp;
    delta := deltab^j*delta;
    // vprintf Shimura : "alpha = %o, beta = %o, i = %o, j = %o, abs(w) = %o\n", alpha, beta, i,j, Abs(wp);

    if not Abs(wp) lt Abs(wpold) then
      // If can't move closer, then must be fixed.
      // assert Abs(Abs(wp)-Abs(wpold)) lt 10^(-prec+2);
      assert Abs(Abs(wp)-Abs(wpold)) lt 10^(-prec/2);
      break;
    end if;
    wpold := wp;
  until j eq 0;

/*
  DD0 := DD!0;
  CCeps := 10^(-prec+2);

  // Check actually belongs to fundamental triangle
  // takes too long, use for debugging only
  assert Argument(wp) ge -pi/a-CCeps and Argument(wp) le pi/a+CCeps and
     &and[Distance(DD0, eps*wp) ge Distance(DD0, wp)+CCeps or
          Abs(Distance(DD0, eps*wp) - Distance(DD0, wp)) lt CCeps : eps in [deltab,deltab^-1]];
*/
  return delta, wp;
end intrinsic;

intrinsic TriangleReduceToFundamentalDomain(Gamma::GrpPSL2, w::SpcHydElt) -> GrpPSL2Elt, SpcHydElt, Any
  {Reduces w to a point wp in the fundamental domain, with the reducing element
   gamma in Gamma such that wp = gamma*w. Returns gamma, wp, and j, where wp lies in the jth translate of the fundamental domain of Delta.}

  require IsTriangleSubgroup(Gamma) : "Gamma must be a triangle subgroup";

  Delta := ContainingTriangleGroup(Gamma);
  delta := TriangleReduceToFundamentalTriangle(Delta, w);

  alphaj, j := TriangleIdentifyCoset(Gamma, delta^-1);
  gamma := alphaj*delta;

  return gamma, gamma*w, j;
end intrinsic;

