intrinsic GetAssignedAttributes(Gamma::GrpPSL2) -> SeqEnum
  {return assigned attributes of Gamma in a sequence.}
  attrs := GetAttributes(Type(Gamma));
  ass := [];
  for attr in attrs do
    if assigned Gamma``attr then
      Append(~ass, attr);
    end if;
  end for;
  return ass;
end intrinsic;

intrinsic NewtonHyperelliptic(Gamma::GrpPSL2 : precstart := 40, precNewton := 1000, bound := 0) -> GrpPSL2
  {wrapper...}
  // numerical data
  Gamma := NewtonHyperellipticGetNumericalData(Gamma : prec := precstart);
  // ramification points
  Gamma := NewtonHyperellipticGetRamificationPoints(Gamma);
  // generate equations
  Gamma := NewtonHyperellipticGetBasicEquations(Gamma);
  // generate rescaling equation
  Gamma := NewtonHyperellipticGetRescalingEquation(Gamma);
  Gamma`TriangleNewtonEquations := Gamma`TriangleNewtonBasicEquations cat [Gamma`TriangleNewtonRescalingEquation];
  // basic initialization values
  Gamma := NewtonHyperellipticGetBasicInitializationValues(Gamma);
  // Newton iteration
  Gamma := NewtonIterate(Gamma, precNewton);
  // recognition
  if bound eq 0 then
    bound := #PassportRepresentatives(Gamma`TriangleSigma); // might not be the best?
  end if;
  Gamma := NewtonHyperellipticRecognize(Gamma : bound := bound); // it's bound to be
  // make Belyi maps
  Gamma := NewtonHyperellipticMakeBelyiMaps(Gamma);
  // return
  return Gamma;
end intrinsic;

intrinsic NewtonHyperellipticGetNumericalData(Gamma::GrpPSL2 : prec := 40) -> GrpPSL2
  {Computes numerical data necessary for Newton, writes it to Gamma and returns Gamma.}
  _:= TriangleUnitDisc(Gamma : Precision := prec);
  // this is what takes time
  ass_bool := assigned Gamma`TriangleNewtonSk and assigned Gamma`TriangleNewtonFD and assigned Gamma`TriangleUnitDisc;
  if not (ass_bool and (Gamma`TriangleUnitDisc)`prec ge prec) then
    Sk := TrianglePowerSeriesBasis(Gamma, 2 : prec := prec, Federalize := true);
  else
    Sk := Gamma`TriangleNewtonSk;
  end if;
  _ := TriangleHyperellipticNumericalCoefficients(Sk, Gamma);
  // assign fundamental domain to Gamma
  DD := TriangleUnitDisc(Gamma : Precision := prec);
  FD := FundamentalDomain(Gamma, DD);
  Gamma`TriangleUnitDisc := DD;
  Gamma`TriangleNewtonFD := FD;
  Gamma`TriangleNewtonSk := Sk;
  return Gamma;
end intrinsic;

intrinsic NewtonHyperellipticGetRamificationPoints(Gamma::GrpPSL2) -> GrpPSL2
  {Assigns TriangleNewtonRamificationPoints0,1,oo to Gamma, a list of pairs [x_p,y_p] (for each of 0,1,oo) on the curve over CC.}
  // pull data from Gamma
  x, y := Explode(Gamma`TriangleNewtonCoordinateSeries);
  FD := Gamma`TriangleNewtonFD;
  Sk := Gamma`TriangleNewtonSk;
  // construct ramification points on the curve
  sigma := Gamma`TriangleSigma;
  sigma_switch := [sigma[1],sigma[3],sigma[2]]; // to make order the same as in FD: white, cross, black
  sigma_cycs := [CycleDecomposition(s) : s in sigma_switch];
  pts := [];
  mults := [];
  for i := 1 to 3 do
    cycs := sigma_cycs[i];
    pts_i := [];
    mults_i := [];
    for cyc in cycs do
      Append(~mults_i, #cyc);
      ind := cyc[1];
      Append(~pts_i, FD[4*(ind-1)+i]);
    end for;
    Append(~pts, pts_i);
    Append(~mults, mults_i);
  end for;
  pts := [pts[1], pts[3], pts[2]]; // now switch back to white, black, cross
  mults := [mults[1], mults[3], mults[2]];
  // delete the point that maps to point at infinity
  Remove(~pts[1],1);
  Remove(~mults[1],1);
  // map points in disc to points on hyperelliptic curve
  pts_X := [];
  for i := 1 to 3 do
    pts_X_i := [];
    for j := 1 to #pts[i] do
      Append(~pts_X_i, [Evaluate(x, ComplexValue(pts[i][j])), Evaluate(y, ComplexValue(pts[i][j]))]); // if pts[i][j] is a pole of x or y this will break
    end for;
    Append(~pts_X, pts_X_i);
  end for;
  // assign points and multiplicities to Gamma
  Gamma`TriangleNewtonRamificationPoints0 := pts_X[1];
  Gamma`TriangleNewtonDiscRamificationPoints0 := pts[1];
  Gamma`TriangleNewtonRamificationMultiplicities0 := mults[1];
  Gamma`TriangleNewtonRamificationPoints1 := pts_X[2];
  Gamma`TriangleNewtonDiscRamificationPoints1 := pts[2];
  Gamma`TriangleNewtonRamificationMultiplicities1 := mults[2];
  Gamma`TriangleNewtonRamificationPointsoo := pts_X[3];
  Gamma`TriangleNewtonDiscRamificationPointsoo := pts[3];
  Gamma`TriangleNewtonRamificationMultiplicitiesoo := mults[3];
  return Gamma;
end intrinsic;

intrinsic HyperellipticTwoTorsionTest(w::SpcHydElt, Gamma::GrpPSL2, Sk::SeqEnum) -> Any
  {}
  // prec := Precision(Parent(w));
  prec := Parent(w)`prec;
  x, y := Explode(Gamma`TriangleNewtonCoordinateSeries);
  pt := [Evaluate(x, ComplexValue(w)), Evaluate(y, ComplexValue(w))];
  vprintf Shimura : "point on curve = %o\n", pt;
  if Abs(pt[2]) lt 10^-(prec/2) then
    vprintf Shimura : "probably a 2-torsion point (of Jacobian).\n";
    return true;
  else
    vprintf Shimura : "probably not a 2-torsion point (of Jacobian).\n";
    return false;
  end if;
end intrinsic;

intrinsic PolarPart(f::RngSerLaurElt) -> RngSerLaurElt
  {}
  // Input: A Laurent series f
  // Output: The polar part of f, i.e., the Laurent tail of f
  new := f + BigO(Parent(f).1^0);
  new := ChangePrecision(new, Infinity());
  return new;
end intrinsic;

/*
intrinsic RiemannRochBasisHyperellipticFormal(m::RngIntElt, Gamma::GrpPSL2, hyperelliptic_polys::SeqEnum) -> Any
  {Basis for L(m*infinity_1)...but formal like}
  v, u := Explode(hyperelliptic_polys);
  g := Genus(Gamma);
  Rx<x> := Parent(v);
  R := BaseRing(Parent(v));
  X := HyperellipticCurve(v,u);
  oo1 := PointsAtInfinity(X)[1];
  if #PointsAtInfinity(X) eq 2 then
    assert Eltseq(oo1)[2] eq -1;
  end if;
  D := Divisor(oo1);
  LD, mLD := RiemannRochSpace(m*D);
  RR_basis := [mLD(el) : el in Basis(LD)];
  Aff := Parent(Numerator(RR_basis[1]));
  ZK := Integers(BaseRing(Parent(Numerator(RR_basis[1]))));
  S := PolynomialRing(ZK, 2);
  assert #GeneratorsSequence(Parent(Numerator(RR_basis[1]))) eq 2;
  h := hom<Aff->S|[S.1, S.2]>;
  return [h(RR_basis[i]) : i in [1..#RR_basis]];
end intrinsic;
*/

intrinsic RiemannRochBasisHyperellipticFormal(m::RngIntElt, Gamma::GrpPSL2, hyperelliptic_polys::SeqEnum) -> Any
  {Basis for L(m*infinity_1)...}
  v, u := Explode(hyperelliptic_polys);
  g := Genus(Gamma);
  R := BaseRing(Parent(v));
  mults_white := Gamma`TriangleNewtonRamificationMultiplicities0;
  mults_black := Gamma`TriangleNewtonRamificationMultiplicities1;
  mults_cross := Gamma`TriangleNewtonRamificationMultiplicitiesoo;
  mult := Max(mults_white cat mults_black cat mults_cross);
  sqrt := R.#GeneratorsSequence(R); // TODO won't work for "special" point
  Rfrac := FieldOfFractions(R);
  Rx<x> := PolynomialRing(Rfrac);
  S<y> := PolynomialRing(Rx);
  basis := [S!1];
  if Degree(u^2 + 4*v) mod 2 eq 1 then // odd case
    for i in [1..Floor(m/2)] do
      Append(~basis, x^i);
    end for;
    if m ge 2*g+1 then
      for i in [0..Floor((m-(2*g+1))/2)] do
        Append(~basis, x^i*y);
      end for;
    end if;
  elif Degree(u^2 + 4*v) mod 2 eq 0 then // even case
    Pow<xi> := LaurentSeriesRing(Rfrac : Precision := 30); // xi stands for x inverse, i.e., x^(-1)
    vv := Evaluate(v,1/xi);
    uu := Evaluate(u,1/xi);
    //D := 1+4*vv/uu^2;
    D := uu^2+4*vv;
    printf "discriminant D = %o\n", D + O(Parent(D).1^mult);
    if assigned Gamma`TriangleNewtonHyperellipticLeadingCoefficient then
      assert Gamma`TriangleNewtonHyperellipticLeadingCoefficient eq LeadingCoefficient(D);
    else
      Gamma`TriangleNewtonHyperellipticLeadingCoefficient := LeadingCoefficient(D); // TODO this function gets called many times.....
    end if;
    D /:= LeadingCoefficient(D);
    printf "after dividing by leading coeff, now D = %o\n", D + O(Parent(D).1^mult);
    D0 := D;
    D := D+O(Parent(D).1^mult);
    yy := (1/2)*(-uu + sqrt*Sqrt(D));
    // not sure if this is the right condition; see corresponding condition in analytic version.
    // want leading coeffs of y_CC and yy to have opposite sign.  I think that lc of y_CC is always -1
    for j in [g+1..m] do
      new := (xi^(-1))^(j-(g+1))*yy;
      new := PolarPart(new);
      new := Evaluate(new,xi^(-1));
      new := Evaluate(new,x);
      new := x^(j-(g+1))*y - new;
      Append(~basis,new);
    end for;
  else
    error "Not even or odd case...???";
  end if;
  return basis;
end intrinsic;

intrinsic NewtonHyperellipticGenericBelyiMap(Gamma::GrpPSL2) -> Any
  {Make generic hyperelliptic Belyi map}

  g := Genus(Gamma);
  s0,t0 := Explode(Gamma`TriangleRiemannRochParameters);
  curve_vars := Gamma`TriangleNewtonVariablesHyperellipticCurveCoefficients;
  R := Parent(curve_vars[1]);
  Rfrac := FieldOfFractions(R);
  S<t> := PolynomialRing(R);
  h := S!0;
  f := S!0;
  for i in [0..2*g+2] do
    f +:= curve_vars[i+1]*t^i;
  end for;
  for i in [0..g+1] do
    h +:= curve_vars[2*g+4+i]*t^i;
  end for;
  num_basis := RiemannRochBasisHyperellipticFormal(t0, Gamma, [f,h]);
  den_basis := RiemannRochBasisHyperellipticFormal(s0+t0, Gamma, [f,h]);
  lc_var := Gamma`TriangleNewtonVariablesLeadingCoefficient;
  num_vars := Gamma`TriangleNewtonVariablesNumeratorCoefficients;
  den_vars := Gamma`TriangleNewtonVariablesDenominatorCoefficients;
  //assert #num_vars eq #num_basis - 1;
  //assert #den_vars eq #den_basis - 1; should these be true...?
  assert #num_basis ge #num_vars;
  assert #den_basis ge #den_vars;
  phi_num := Parent(den_vars[1])!0;
  for i := 1 to #num_vars do
    phi_num := phi_num + num_vars[i]*num_basis[i];
  end for;
  phi_num := phi_num + num_basis[#num_vars+1];
  phi_den := Parent(den_vars[1])!0;
  for i := 1 to #den_vars do
    phi_den := phi_den + den_vars[i]*den_basis[i];
  end for;
  phi_den := phi_den + den_basis[#den_vars+1];
  // TODO: Convert to function field in two variables; see line 445
  F<x,y> := FunctionField(Rfrac,2);
  coeffs_num := Coefficients(phi_num);
  coeffs_num_eval_x := [ Evaluate(coeffs_num[i], x) : i in [1..#coeffs_num] ];
  phi_num := F!0;
  for i := 1 to #coeffs_num_eval_x do
    phi_num +:= coeffs_num_eval_x[i]*F!(y)^(i-1);
  end for;

  coeffs_den := Coefficients(phi_den);
  coeffs_den_eval_x := [ Evaluate(coeffs_den[i], x) : i in [1..#coeffs_den] ];
  phi_den := F!0;
  for i := 1 to #coeffs_den_eval_x do
    phi_den +:= coeffs_den_eval_x[i]*F!(y)^(i-1);
  end for;
  phi := lc_var*phi_num/phi_den;
  return phi;
end intrinsic;

intrinsic NewtonHyperellipticVanishingEquations(Gamma::GrpPSL2) -> Any
  {}
  // setup
    white_vars := Gamma`TriangleNewtonVariables0;
    mults_white := Gamma`TriangleNewtonRamificationMultiplicities0;
    black_vars := Gamma`TriangleNewtonVariables1;
    mults_black := Gamma`TriangleNewtonRamificationMultiplicities1;
    cross_vars := Gamma`TriangleNewtonVariablesoo;
    mults_cross := Gamma`TriangleNewtonRamificationMultiplicitiesoo;
    curve_vars := Gamma`TriangleNewtonVariablesHyperellipticCurveCoefficients;
    lc_var := Gamma`TriangleNewtonVariablesLeadingCoefficient;
    num_vars := Gamma`TriangleNewtonVariablesNumeratorCoefficients;
    den_vars := Gamma`TriangleNewtonVariablesDenominatorCoefficients;
    Sk := Gamma`TriangleNewtonSk;
    d := Gamma`TriangleD;
    g := Genus(Gamma);
    sigma := Gamma`TriangleSigma;
    s0 := #CycleDecomposition(sigma[1])[1];
    t0 := d-s0+1;
    R := Parent(lc_var);
    Rfrac := FieldOfFractions(R);
  // make hyperelliptic polys
    S<xx> := PolynomialRing(R);
    h := S!0;
    f := S!0;
    for i in [0..2*g+2] do
      f +:= curve_vars[i+1]*xx^i;
    end for;
    for i in [0..g+1] do
      h +:= curve_vars[2*g+4+i]*xx^i;
    end for;
  mult := Max(mults_white cat mults_black cat mults_cross);
  // Ser<t> := LaurentSeriesRing(Rfrac : Precision := 10*d*mult);
  // Ser<t> := LaurentSeriesRing(Rfrac : Precision := 50);
  Ser<t> := LaurentSeriesRing(Rfrac);
  equations := [];
  // white equations
  vprintf Shimura : "White dots:\n";
  for k := 1 to #white_vars do
    w := Gamma`TriangleNewtonDiscRamificationPoints0[k];
    pt := white_vars[k];
    x_p := Ser!pt[1];
    y_p := Ser!pt[2];
    if not HyperellipticTwoTorsionTest(w, Gamma, Sk) then // x-xp is local uniformizer t
      B := 2*y_p+Evaluate(h, t+x_p);
      C := y_p^2+Evaluate(h, t+x_p)*y_p - Evaluate(f, t+x_p);
      C -:= Coefficient(C,0);
      B0 := B;
      C0 := C;
      B := B+O(t^mult);
      C := C+O(t^mult);
      u := -B+B*Sqrt(1-4*C/(B^2)); // plus or minus???????
      // numerator
      num_basis := RiemannRochBasisHyperellipticFormal(t0, Gamma, [f,h]);
      num := Parent(num_basis[1])!0;
      // num := Ser!0;
      for i := 1 to #num_vars do // numerator monomials except leading term
        num +:= num_vars[i]*num_basis[i];
      end for;
      if (#num_vars+1) eq 1 then // numerator just has constant term (which doesn't appear in num_vars)
        num +:= 1;
      else
        num +:= num_basis[#num_vars+1]; 
      end if;
      coeffs_num := Coefficients(num);
      coeffs_num_eval_x := [ Evaluate(coeffs_num[i], t+x_p) : i in [1..#coeffs_num] ];
      num_eval := Ser!0;
      for i := 1 to #coeffs_num_eval_x do
        num_eval +:= coeffs_num_eval_x[i]*Ser!(u+y_p)^(i-1);
      end for;
      // FIXME: should probably get rid of this---multiplying by lc change vanishing
      num_eval *:= -lc_var; // negative because TriangleGenusOneNumericalBelyiMap outputs NEGATIVES of numerator coeffs
    else // y is local uniformizer t
      error "Not implemented yet for Weierstrass points";
      /*
      // update ramification point: y-coordinate should be zero if 2-torsion
      Gamma`TriangleNewtonRamificationPoints0[k][2] := Parent(Gamma`TriangleNewtonRamificationPoints0[k][2])!0;
      Append(~equations, R!y_p);
      Rs<s> := PolynomialRing(Ser);
      f := s^3 + 3*x_p*s^2 + (3*x_p^2 - 27*c4)*s - t^2;
      fp := Derivative(f);
      s_is := [Ser!0];
      for i := 1 to d*mult do // hack
        new := s_is[i] - Evaluate(f,s_is[i])/Evaluate(fp,s_is[i]);
        Append(~s_is, new);
      end for;
      // both of these should give y^2 if the answer is right
      ss := s_is[#s_is];
      assert IsWeaklyEqual(ss^3 + 3*x_p*ss^2 + (3*x_p^2 - 27*c4)*ss, t^2);
      num := Ser!0;
      for i := 1 to #num_vars do // numerator monomials except leading term
        if i mod 2 eq 0 then
          num +:= num_vars[i]*(ss+x_p)^(i/2);
        elif i eq 1 then
          num +:= num_vars[i];
        else // i>1 odd
          num +:= num_vars[i]*(ss+x_p)^((i-3) div 2)*(t+y_p);
        end if;
      end for;
      if (#num_vars+1) eq 1 then // numerator just has constant term (which doesn't appear in num_vars)
        num +:= 1;
      elif (#num_vars+1) mod 2 eq 0 then // numerator leading term
        num +:= (ss+x_p)^((#num_vars+1)/2);
      else
        num +:= (ss+x_p)^((#num_vars+1-3) div 2)*(t+y_p);
      end if;
      // FIXME: should probably get rid of this---multiplying by lc change vanishing
      num *:= -lc_var; // negative because TriangleGenusOneNumericalBelyiMap outputs NEGATIVES of numerator coeffs
      */
    end if;
    phi0 := num_eval;
    for j := 0 to mults_white[k]-1 do // vanish to order mults_white[k]
      Append(~equations, R!Numerator(Rfrac!Coefficient(phi0, j)));
    end for;
  end for;
  // black equations: remember that TriangleGenusOneNumericalBelyiMap outputs NEGATIVES of numerator coeffs
  vprintf Shimura : "Black dots:\n";
  for k := 1 to #black_vars do
    w := Gamma`TriangleNewtonDiscRamificationPoints1[k];
    pt := black_vars[k];
    x_p := Ser!pt[1];
    y_p := Ser!pt[2];
    if not HyperellipticTwoTorsionTest(w, Gamma, Sk) then // x-xp is local uniformizer t
      B := 2*y_p+Evaluate(h, t+x_p);
      C := y_p^2+Evaluate(h, t+x_p)*y_p - Evaluate(f, t+x_p);
      C -:= Coefficient(C,0);
      B0 := B;
      C0 := C;
      B := B+O(t^mult);
      C := C+O(t^mult);
      u := -B+B*Sqrt(1-4*C/(B^2)); // plus or minus???????
      /*
        Rs<s> := PolynomialRing(Ser);
        // y^2 + h(x)*y = f(x)
        F := (s+y_p)^2 + Evaluate(h, t+x_p)*(s+y_p) - Evaluate(f, t+x_p); 
        Fp := Derivative(F);
        vprintf Shimura : "Computing 1/f'...";
        t0 := Cputime();
        Fpinv := 1/Fp;
        t1 := Cputime();
        vprint Shimura : "done. %o seconds.\n", t1-t0;
        s_is := [Ser!0];
        for i := 1 to d*mult do // hack
          vprintf Shimura : "Hensel iteration %o out of %o: ", i, d*mult;
          time0 := Cputime();
          // new := s_is[i] - Evaluate(F,s_is[i])/Evaluate(Fp,s_is[i]);
          new := s_is[i] - Evaluate(F,s_is[i])*Evaluate(Fpinv,s_is[i]);
          Append(~s_is, new);
          time1 := Cputime();
          vprintf Shimura : "done %o seconds.\n", time1-time0;
        end for;
        // both of these should give y^2 if the answer is right
        ss := s_is[#s_is];
        assert IsWeaklyZero((ss+y_p)^2 + Evaluate(h, t+x_p)*(ss+y_p) - Evaluate(f, t+x_p));
      */
      // numerator
        num_basis := RiemannRochBasisHyperellipticFormal(t0, Gamma, [f,h]);
        num := Parent(num_basis[1])!0;
        // num := Ser!0;
        for i := 1 to #num_vars do // numerator monomials except leading term
          num +:= num_vars[i]*num_basis[i];
        end for;
        if (#num_vars+1) eq 1 then // numerator just has constant term (which doesn't appear in num_vars)
          num +:= 1;
        else
          num +:= num_basis[#num_vars+1]; 
        end if;
        coeffs_num := Coefficients(num);
        coeffs_num_eval_x := [ Evaluate(coeffs_num[i], t+x_p) : i in [1..#coeffs_num] ];
        num_eval := Ser!0;
        for i := 1 to #coeffs_num_eval_x do
          num_eval +:= coeffs_num_eval_x[i]*Ser!(u+y_p)^(i-1);
        end for;
        // FIXME: should probably get rid of this---multiplying by lc change vanishing
        num_eval *:= -lc_var; // negative because TriangleGenusOneNumericalBelyiMap outputs NEGATIVES of numerator coeffs
      // denominator 
        den_basis := RiemannRochBasisHyperellipticFormal(s0+t0, Gamma, [f,h]);
        // den := Ser!0;
        den := Parent(den_basis[1])!0;
        for i := 1 to #den_vars do // denominator monomials except leading term
          den +:= den_vars[i]*den_basis[i];
        end for;
        if (#den_vars+1) eq 1 then // denominator just has constant term (which doesn't appear in num_vars)
          den +:= 1;
        else
          den +:= den_basis[#den_vars+1]; 
        end if;
        coeffs_den := Coefficients(den);
        coeffs_den_eval_x := [ Evaluate(coeffs_den[i], t+x_p) : i in [1..#coeffs_den] ];
        den_eval := Ser!0;
        for i := 1 to #coeffs_den_eval_x do
          den_eval +:= coeffs_den_eval_x[i]*Ser!(u+y_p)^(i-1);
        end for;
    else // y is local uniformizer t
      error "Not implemented yet for Weierstrass points";
      /*
      // update ramification point: y-coordinate should be zero if 2-torsion
      Gamma`TriangleNewtonRamificationPoints0[k][2] := Parent(Gamma`TriangleNewtonRamificationPoints0[k][2])!0;
      Append(~equations, R!y_p);
      Rs<s> := PolynomialRing(Ser);
      f := s^3 + 3*x_p*s^2 + (3*x_p^2 - 27*c4)*s - t^2;
      fp := Derivative(f);
      s_is := [Ser!0];
      for i := 1 to d*mult do // hack
        new := s_is[i] - Evaluate(f,s_is[i])/Evaluate(fp,s_is[i]);
        Append(~s_is, new);
      end for;
      // both of these should give y^2 if the answer is right
      ss := s_is[#s_is];
      assert IsWeaklyEqual(ss^3 + 3*x_p*ss^2 + (3*x_p^2 - 27*c4)*ss, t^2);
      num := Ser!0;
      for i := 1 to #num_vars do // numerator monomials except leading term
        if i mod 2 eq 0 then
          num +:= num_vars[i]*(ss+x_p)^(i/2);
        elif i eq 1 then
          num +:= num_vars[i];
        else // i>1 odd
          num +:= num_vars[i]*(ss+x_p)^((i-3) div 2)*(t+y_p);
        end if;
      end for;
      if (#num_vars+1) eq 1 then // numerator just has constant term (which doesn't appear in num_vars)
        num +:= 1;
      elif (#num_vars+1) mod 2 eq 0 then // numerator leading term
        num +:= (ss+x_p)^((#num_vars+1)/2);
      else
        num +:= (ss+x_p)^((#num_vars+1-3) div 2)*(t+y_p);
      end if;
      // FIXME: should probably get rid of this---multiplying by lc change vanishing
      num *:= -lc_var; // negative because TriangleGenusOneNumericalBelyiMap outputs NEGATIVES of numerator coeffs
      */
    end if;
    // -lc(num)-(den)
    phi1 := num_eval - den_eval;
    for j := 0 to mults_black[k]-1 do // vanish to order mults_black[k]
      Append(~equations, R!Numerator(Rfrac!Coefficient(phi1, j)));
    end for;
  end for;
  // cross equations
  vprintf Shimura : "Cross points:\n";
  for k := 1 to #cross_vars do
    w := Gamma`TriangleNewtonDiscRamificationPointsoo[k];
    pt := cross_vars[k];
    x_p := Ser!pt[1];
    y_p := Ser!pt[2];
    if not HyperellipticTwoTorsionTest(w, Gamma, Sk) then // x-xp is local uniformizer t
      B := 2*y_p+Evaluate(h, t+x_p);
      C := y_p^2+Evaluate(h, t+x_p)*y_p - Evaluate(f, t+x_p);
      C -:= Coefficient(C, 0);
      B0 := B;
      C0 := C;
      B := B+O(t^mult);
      C := C+O(t^mult);
      u := -B+B*Sqrt(1-4*C/(B^2)); // plus or minus???????
      // denominator 
        den_basis := RiemannRochBasisHyperellipticFormal(s0+t0, Gamma, [f,h]);
        // den := Ser!0;
        den := Parent(den_basis[1])!0;
        for i := 1 to #den_vars do // denominator monomials except leading term
          den +:= den_vars[i]*den_basis[i];
        end for;
        if (#den_vars+1) eq 1 then // denominator just has constant term (which doesn't appear in num_vars)
          den +:= 1;
        else
          den +:= den_basis[#den_vars+1]; 
        end if;
        coeffs_den := Coefficients(den);
        coeffs_den_eval_x := [ Evaluate(coeffs_den[i], t+x_p) : i in [1..#coeffs_den] ];
        den_eval := Ser!0;
        for i := 1 to #coeffs_den_eval_x do
          den_eval +:= coeffs_den_eval_x[i]*Ser!(u+y_p)^(i-1);
        end for;
    else // y is local uniformizer t
      error "Not implemented yet for Weierstrass points";
      /*
      // update ramification point: y-coordinate should be zero if 2-torsion
      Gamma`TriangleNewtonRamificationPoints0[k][2] := Parent(Gamma`TriangleNewtonRamificationPoints0[k][2])!0;
      Append(~equations, R!y_p);
      Rs<s> := PolynomialRing(Ser);
      f := s^3 + 3*x_p*s^2 + (3*x_p^2 - 27*c4)*s - t^2;
      fp := Derivative(f);
      s_is := [Ser!0];
      for i := 1 to d*mult do // hack
        new := s_is[i] - Evaluate(f,s_is[i])/Evaluate(fp,s_is[i]);
        Append(~s_is, new);
      end for;
      // both of these should give y^2 if the answer is right
      ss := s_is[#s_is];
      assert IsWeaklyEqual(ss^3 + 3*x_p*ss^2 + (3*x_p^2 - 27*c4)*ss, t^2);
      num := Ser!0;
      for i := 1 to #num_vars do // numerator monomials except leading term
        if i mod 2 eq 0 then
          num +:= num_vars[i]*(ss+x_p)^(i/2);
        elif i eq 1 then
          num +:= num_vars[i];
        else // i>1 odd
          num +:= num_vars[i]*(ss+x_p)^((i-3) div 2)*(t+y_p);
        end if;
      end for;
      if (#num_vars+1) eq 1 then // numerator just has constant term (which doesn't appear in num_vars)
        num +:= 1;
      elif (#num_vars+1) mod 2 eq 0 then // numerator leading term
        num +:= (ss+x_p)^((#num_vars+1)/2);
      else
        num +:= (ss+x_p)^((#num_vars+1-3) div 2)*(t+y_p);
      end if;
      // FIXME: should probably get rid of this---multiplying by lc change vanishing
      num *:= -lc_var; // negative because TriangleGenusOneNumericalBelyiMap outputs NEGATIVES of numerator coeffs
      */
    end if;
    phioo := den_eval;
    for j := 0 to mults_cross[k]-1 do // vanish to order mults_cross[k]
      Append(~equations, R!Numerator(Rfrac!Coefficient(phioo, j)));
    end for;
  end for;
  return equations;
end intrinsic;

intrinsic NewtonHyperellipticGetBasicEquations(Gamma::GrpPSL2) -> GrpPSL2
  {Computes basic Newton equations (ramification, order of vanishing) and assigns them to Gamma.}
  // the s and the t
    sigma := Gamma`TriangleSigma;
    d := Gamma`TriangleD;
    g := Genus(Gamma);
    s := #CycleDecomposition(sigma[1])[1];
  // number of points is also number of mults
  // pull multiplicities from Gamma
    mults_white := Gamma`TriangleNewtonRamificationMultiplicities0;
    mults_black := Gamma`TriangleNewtonRamificationMultiplicities1;
    mults_cross := Gamma`TriangleNewtonRamificationMultiplicitiesoo;
    num_points := #mults_white+#mults_black+#mults_cross;
    num_coeffs_CC := Gamma`TriangleNumericalBelyiMapNumeratorCoefficients;
    den_coeffs_CC := Gamma`TriangleNumericalBelyiMapDenominatorCoefficients;
    curve_coeffs_CC := Gamma`TriangleNumericalCurveCoefficients;
  // generate polynomial ring
    var_names := [];
    for i := 1 to #curve_coeffs_CC-1 do // don't need y^2 coefficient
      Append(~var_names, Sprintf("c%o", i));
    end for;
    for i := 1 to #mults_white do
      Append(~var_names, Sprintf("x%o_w", i));
      Append(~var_names, Sprintf("y%o_w", i));
    end for;
    for i := 1 to #mults_black do
      Append(~var_names, Sprintf("x%o_b", i));
      Append(~var_names, Sprintf("y%o_b", i));
    end for;
    for i := 1 to #mults_cross do
      Append(~var_names, Sprintf("x%o_c", i));
      Append(~var_names, Sprintf("y%o_c", i));
    end for;
    Append(~var_names, "lc");
    for i := 1 to #num_coeffs_CC-1 do // assume numerator is monic, TODO what about when t is 1?!?!
      if i eq 1 then
        Append(~var_names, Sprintf("a%o", 0));
      else
        Append(~var_names, Sprintf("a%o", i));
      end if;
    end for;
    for i := 1 to #den_coeffs_CC-1 do // assume denominator is monic
      if i eq 1 then
        Append(~var_names, Sprintf("b%o", 0));
      else
        Append(~var_names, Sprintf("b%o", i));
      end if;
    end for;
    // variable for sqrt
    Append(~var_names, "sqrt");
    // make special point variables if we need to
    /*
    if s lt d then
      Append(~var_names, "x_s");
      Append(~var_names, "y_s");
    end if;
    */
  // make R
    R := PolynomialRing(Rationals(), #var_names, "grevlex");
    AssignNames(~R, var_names);
    // make pairs for points variables cuz...jeez
    curve_vars := [R.i : i in [1..#curve_coeffs_CC-1]];
    white_vars := []; // pairs [x1_w, y1_w],...
    for i := 0 to #mults_white-1 do
      x_ind := #curve_coeffs_CC-1+2*i+1;
      y_ind := #curve_coeffs_CC-1+2*i+2;
      Append(~white_vars, [R.x_ind, R.y_ind]);
    end for;
    black_vars := []; // pairs [x1_b, y1_b],...
    for i := 0 to #mults_black-1 do
      x_ind := #curve_coeffs_CC-1+2*#mults_white+2*i+1;
      y_ind := #curve_coeffs_CC-1+2*#mults_white+2*i+2;
      Append(~black_vars, [R.x_ind, R.y_ind]);
    end for;
    cross_vars := [];
    for i := 0 to #mults_cross-1 do
      x_ind := #curve_coeffs_CC-1+2*#mults_white+2*#mults_black+2*i+1;
      y_ind := #curve_coeffs_CC-1+2*#mults_white+2*#mults_black+2*i+2;
      Append(~cross_vars, [R.x_ind, R.y_ind]);
    end for;
    vprintf Shimura : "white vars = %o\n", white_vars;
    vprintf Shimura : "black vars = %o\n", black_vars;
    vprintf Shimura : "cross vars = %o\n", cross_vars;
    // make lists of variables for coefficients of Belyi map
    lc_ind := #curve_coeffs_CC-1+2*num_points+1;
    lc_var := R.lc_ind;
    num_vars := [];
    for i := 1 to #num_coeffs_CC-1 do
      ind := #curve_coeffs_CC-1+2*num_points+1+i;
      Append(~num_vars, R.ind);
    end for;
    vprintf Shimura : "R = %o\n", R;
    den_vars := [];
    for i := 1 to #den_coeffs_CC-1 do
      ind := #curve_coeffs_CC-1+2*num_points+1+#num_vars+i;
      Append(~den_vars, R.ind);
    end for;
    vprintf Shimura : "num vars = %o\n", num_vars;
    vprintf Shimura : "den vars = %o\n", den_vars;
    /*
    if s lt d then
      special_vars := [];
      Append(~special_vars, R.(#var_names-1));
      Append(~special_vars, R.#var_names);
    end if;
    */
    // make the equations
    equations := [];
    Rfrac := FieldOfFractions(R);
  // assign VARS to Gamma
    Gamma`TriangleNewtonVariablesHyperellipticCurveCoefficients := curve_vars;
    Gamma`TriangleNewtonVariables0 := white_vars;
    Gamma`TriangleNewtonVariables1 := black_vars;
    Gamma`TriangleNewtonVariablesoo := cross_vars;
    Gamma`TriangleNewtonVariablesLeadingCoefficient := lc_var;
    Gamma`TriangleNewtonVariablesNumeratorCoefficients := num_vars;
    Gamma`TriangleNewtonVariablesDenominatorCoefficients := den_vars;
  // equations for the points
    for pt_list in [white_vars, black_vars, cross_vars] do
      i := 1;
      while i le #pt_list do
        pt := pt_list[i];
        u := R!0;
        v := R!0;
        for i in [0..2*g+2] do
          v +:= curve_vars[i+1]*pt[1]^i;
        end for;
        for i in [0..g+1] do
          u +:= curve_vars[2*g+4+i]*pt[1]^i;
        end for;
        Append(~equations, pt[2]^2+u*pt[2]-v);
        i := i+1;
      end while;
    end for;
  print Parent(equations[1]); //printing
  // equations for ramification
  //equations cat:= NewtonHyperellipticVanishingEquations(Gamma);
  // special equations
    /*
    if s lt d then
      pt := special_vars;
      x_s := R!pt[1];
      y_s := R!pt[2];
      phi_den := R!0;
      for i := 1 to #den_vars do // denominator monomials except leading term
        if i mod 2 eq 0 then
          phi_den +:= den_vars[i]*x_s^(i div 2);
        elif i eq 1 then
          phi_den +:= den_vars[i];
        else // i>1 odd
          phi_den +:= den_vars[i]*x_s^((i-3) div 2)*y_s;
        end if;
      end for;
      if #den_vars+1 eq 1 then
        phi_den +:= 1; // Belyi map is polynomial
      elif (#den_vars+1) mod 2 eq 0 then // denominator leading term
        phi_den +:= x_s^((#den_vars+1) div 2);
      else
        phi_den +:= x_s^((#den_vars+1-3) div 2)*y_s;
      end if;
      phi_num := R!0;
      for i := 1 to #num_vars do // numerator monomials except leading term
        if i mod 2 eq 0 then
          phi_num +:= num_vars[i]*x_s^(i div 2);
        elif i eq 1 then
          phi_num +:= num_vars[i];
        else // i>1 odd
          phi_num +:= num_vars[i]*x_s^((i-3) div 2)*y_s;
        end if;
      end for;
      if (#num_vars+1) eq 1 then // numerator just has constant term (which doesn't appear in num_vars)
        phi_num +:= 1;
      elif (#num_vars+1) mod 2 eq 0 then // numerator leading term
        phi_num +:= x_s^((#num_vars+1) div 2);
      else
        phi_num +:= x_s^((#num_vars+1-3) div 2)*y_s;
      end if;
      phi_num *:= -lc_var; // negative because TriangleGenusOneNumericalBelyiMap outputs NEGATIVES of numerator coeffs
      Append(~equations, pt[2]^2-(pt[1]^3-27*inv_vars[1]*pt[1]-54*inv_vars[2]));
      Append(~equations, phi_num);
      Append(~equations, phi_den);
      print Parent(equations[1]); // printing
      // Append(~equations, R!(pt[2]^2-(pt[1]^3-27*inv_vars[1]*pt[1]-54*inv_vars[2])));
      // Append(~equations, R!Numerator(Rfrac!(phi_num)));
      // Append(~equations, R!Numerator(Rfrac!(phi_den)));
    end if;
    */
  // assign to Gamma
  /*
  if s lt d then
    Gamma`TriangleNewtonVariablesSpecial := special_vars;
  end if;
  */
  Gamma`TriangleNewtonBasicEquations := equations;
  return Gamma;
end intrinsic;

// TODO
intrinsic NewtonHyperellipticGetBasicInitializationValues(Gamma::GrpPSL2) -> GrpPSL2
  {Assigns start_vector [c4, c6, points0, points1, pointsoo, extra_points, lc, num_coeffs, den_coeffs] to Gamma.}
  // assertions
  assert assigned Gamma`TriangleNumericalPrecision;
  // lc
  lc := Gamma`TriangleNumericalBelyiMapLeadingCoefficient;
  // num_coeffs: numerator coeffs of Belyi map
  num_coeffs := Gamma`TriangleNumericalBelyiMapNumeratorCoefficients;
  // den_coeffs: denominator coeffs of Belyi map
  den_coeffs := Gamma`TriangleNumericalBelyiMapDenominatorCoefficients;
  Gamma`TriangleNewtonInitializationNumeratorCoefficients := num_coeffs;
  Gamma`TriangleNewtonInitializationDenominatorCoefficients := den_coeffs;
  curve_coeffs := Gamma`TriangleNumericalCurveCoefficients;
  Remove(~curve_coeffs, #curve_coeffs);
  g := Genus(Gamma);
  for i := 1 to 2*g+3 do
    curve_coeffs[i] := -curve_coeffs[i];
  end for;
  /*
    // special points
    sigma := Gamma`TriangleSigma;
    d := Gamma`TriangleD;
    s := #CycleDecomposition(sigma[1])[1];
    if s eq d then // TODO hack
      t := 0;
    else
      t := d-s+1;
    end if;
    CC<I> := Parent(den_coeffs[1]);
    prec := Precision(CC);
    if s lt d then
      vprint Shimura: "Not totally ramified, so trying to find common zero of numerator and denominator...";
      Rx<x> := PolynomialRing(CC);
      Ry<y> := PolynomialRing(Rx);
      phi_den := Ry!0;
      for i := 1 to #den_coeffs do
        if i mod 2 eq 0 then
          phi_den +:= den_coeffs[i]*x^(i div 2);
        elif i eq 1 then
          phi_den +:= den_coeffs[i];
        else // i>1 odd
          phi_den +:= den_coeffs[i]*x^((i-3) div 2)*y;
        end if;
      end for;
      phi_num := Ry!0;
      for i := 1 to #num_coeffs do
        if i mod 2 eq 0 then
          phi_num +:= num_coeffs[i]*x^(i div 2);
        elif i eq 1 then
          phi_num +:= num_coeffs[i];
        else // i>1 odd
          phi_num +:= num_coeffs[i]*x^((i-3) div 2)*y;
        end if;
      end for;
      phi_num *:= -lc; // negative because TriangleGenusOneNumericalBelyiMap outputs NEGATIVES of numerator coeffs
      c0 := Coefficient(phi_num, 0);
      //printf "constant coefficient of numerator = %o\n", Coefficient(c0,0);
      //print Abs(Coefficient(c0,0));
      //printf "linear coefficient of numerator = %o\n", Coefficient(c0,1);
      c1 := Coefficient(phi_num, 1);
      eqn_num := c0^2-c1^2*(x^3-27*c4*x-54*c6);
      d0 := Coefficient(phi_den, 0);
      d1 := Coefficient(phi_den, 1);
      eqn_den := d0^2-d1^2*(x^3-27*c4*x-54*c6);
      vprintf Shimura : "Numerator :\n%o\n", phi_num;
      vprintf Shimura : "Denominator :\n%o\n", phi_den;
      roots_num := Roots(eqn_num);
      roots_den := Roots(eqn_den);
      common_bool := false;
      for i := 1 to #roots_num do // looking for common roots of num and den
        a := roots_num[i][1];
        vprintf Shimura : "numerator root = %o\n", a;
        for j := 1 to #roots_den do
          b := roots_den[j][1];
          vprintf Shimura : "\tdenominator root = %o\n", b;
          if Abs(a-b) lt 10^(-prec/4) then // wild guess
            common_bool := true;
            a0 := a;
            b0 := b;
            vprintf Shimura : "Common zero found!\nError = %o\n", Abs(a0-b0);
            vprintf Shimura : "Numerator root = %o\n", a0;
            vprintf Shimura : "Denominator root = %o\n\n", b0;
          end if;
        end for;
      end for;
      if not common_bool then
        error "No common zero found! :(";
      end if;
      vprintf Shimura : "Computing y-value of zero...\n";
      xs := a0;
      ys := Sqrt(xs^3 - 27*c4*xs - 54*c6);
      eval_num := Evaluate(Evaluate(phi_num,ys),xs);
      eval_den := Evaluate(Evaluate(phi_den,ys),xs);
      if (Abs(eval_num) gt 10^(-prec/4)) or (Abs(eval_den) gt 10^(-prec/4)) then
        ys := -ys;
      end if;
      eval_num := Evaluate(Evaluate(phi_num,ys),xs);
      eval_den := Evaluate(Evaluate(phi_den,ys),xs);
      vprintf Shimura : "error of numerator evaluated at common zero: %o\n", Abs(eval_num);
      vprintf Shimura : "error of denominator evaluated at common zero: %o\n", Abs(eval_den);
      // who knows how close they should be?
      // assert Abs(eval_num) lt 10^(-prec/4);
      // assert Abs(eval_den) lt 10^(-prec/4);
      vprintf Shimura : "Common zero = %o\n", [xs, ys];
      Gamma`TriangleNewtonInitializationSpecialPoint := [xs, ys];
    end if;
  */
  // assign stuff to Gamma
  white := [];
  black := [];
  cross := [];
  for i := 1 to #Gamma`TriangleNewtonRamificationPoints0 do
    Append(~white, Gamma`TriangleNewtonRamificationPoints0[i][1]);
    Append(~white, Gamma`TriangleNewtonRamificationPoints0[i][2]);
  end for;
  for i := 1 to #Gamma`TriangleNewtonRamificationPoints1 do
    Append(~black, Gamma`TriangleNewtonRamificationPoints1[i][1]);
    Append(~black, Gamma`TriangleNewtonRamificationPoints1[i][2]);
  end for;
  for i := 1 to #Gamma`TriangleNewtonRamificationPointsoo do
    Append(~cross, Gamma`TriangleNewtonRamificationPointsoo[i][1]);
    Append(~cross, Gamma`TriangleNewtonRamificationPointsoo[i][2]);
  end for;
  lc := Gamma`TriangleNumericalBelyiMapLeadingCoefficient;
  num := Gamma`TriangleNewtonInitializationNumeratorCoefficients;
  Remove(~num, #num);
  den := Gamma`TriangleNewtonInitializationDenominatorCoefficients;
  Remove(~den, #den);
  // no special points
  /*
  if s lt d then
    start := [c4, c6] cat white cat black cat cross cat [lc] cat num cat den cat [xs, ys];
  else
    start := [c4, c6] cat white cat black cat cross cat [lc] cat num cat den;
  end if;
  */
  // sqrt...squared?
  
  start := curve_coeffs cat white cat black cat cross cat [lc] cat num cat den;
  Gamma`TriangleNewtonInitialization := start;
  return Gamma;
end intrinsic;

// TODO
intrinsic NewtonHyperellipticGetRescalingEquation(Gamma::GrpPSL2) -> GrpPSL2
  {assign (polynomial equation for rescaling) to Gamma.}
  // setup
    basic_equations := Gamma`TriangleNewtonBasicEquations;
    R := Parent(basic_equations[1]);
    Rfrac := FieldOfFractions(R);
    lc_var := Gamma`TriangleNewtonVariablesLeadingCoefficient;
    num_vars := Gamma`TriangleNewtonVariablesNumeratorCoefficients;
    den_vars := Gamma`TriangleNewtonVariablesDenominatorCoefficients;
    rescaling := Gamma`TriangleNewtonRescalingData; // [* gcd, wts, nonzero_inds, nonzero_vals *]
    num_coeffs := Gamma`TriangleNumericalBelyiMapNumeratorCoefficients;
    assert Parent(lc_var) eq R;
  // rescaling
    gcd, wts, nonzero_inds, nonzero_vals := Explode(rescaling);
    lc_exponent := 0;
    for i := 1 to #wts do
      if nonzero_inds[i] le #num_coeffs then
        lc_exponent +:= wts[i];
      end if;
    end for;
    vprintf Shimura : "wts = %o\n", wts;
    assert #nonzero_inds eq #wts;
    rescaling_equation := R!1;
    wts_sum := &+[wts[i] : i in [1..#wts]];
    assert wts_sum eq 0;
    map_vars := num_vars cat [R!1] cat den_vars cat [R!1];
    for i := 1 to #wts do
      rescaling_equation *:= Rfrac!(map_vars[nonzero_inds[i]])^wts[i];
      // vprintf Shimura : "i=%o, equation=%o\n", i, rescaling_equation;
    end for;
    // lc
    printf "rescaling before = %o\n", rescaling_equation;
    printf "wts = %o\n", wts;
    printf "#num_coeffs = %o\n", #num_coeffs;
    printf "nonzero_inds = %o\n", nonzero_inds;
    printf "lc_exponent = %o\n", lc_exponent;
    rescaling_equation *:= Rfrac!(lc_var)^lc_exponent;
    printf "rescaling after = %o\n", rescaling_equation;
  // assign to Gamma and return
    Gamma`TriangleNewtonRescalingEquation := R!Numerator(rescaling_equation-1);
    return Gamma;
end intrinsic;

intrinsic NewtonIterate(equations::SeqEnum[RngMPolElt], start::SeqEnum[FldComElt], precNewton::RngIntElt) -> SeqEnum[FldComElt]
  {Newton iterate starting solution to equations (polynomials) to get a solution to precision precNewton.}
  // TODO assertions?
  vprintf Shimura : "#start = %o\n", #start;
  R := Parent(equations[1]);
  vars := GeneratorsSequence(R);
  vprintf Shimura : "variables = %o\n", vars;
  // make Jacobian
  J := ZeroMatrix(R, #vars, #equations);
  for i := 1 to #vars do
    for j := 1 to #equations do
      J[i,j] := Derivative(equations[j], i); // mind your is and js
    end for;
  end for;
  vprintf Shimura : "Ncols(J) = %o, Nrows(J) = %o, #start = %o\n", Ncols(J), Nrows(J), #start;
  vprintf Shimura : "#vars = %o, #equations = %o\n", #vars, #equations;
  assert Ncols(J) ge Nrows(J);
  assert Nrows(J) eq #start;
  precstart := Precision(Parent(start[1]));
  prec := precstart;
  solvec := ChangeRing(Vector(start), ComplexField(prec)); // solvec is the solution vector that Newton updates
  err := Max([Abs(Evaluate(eqn, Eltseq(start))) : eqn in equations]);
  /*
  err := Max([Abs(Evaluate(eqn, Eltseq(start))) : eqn in equations]);
  prec := Floor(-Log(10,err));
  solvec := ChangeRing(Vector(start), ComplexField(prec)); // solvec is the solution vector that Newton updates
  */
  for i := 1 to 50 do
    // update solvec precision
    solvec := ChangeRing(solvec, ComplexField(prec));
    // compute error and prec
    vprintf Shimura : "Newton iteration %o:\n", i;
    errors := [Abs(Evaluate(eqn, Eltseq(solvec))) : eqn in equations];
    err := Max(errors);
    err_ind := Index(errors, err);
    vprintf Shimura : "err = %o\n", err;
    vprintf Shimura : "equation[%o], %o, had largest error:\n%o\n", err_ind, equations[err_ind], err;
    if prec ge precNewton then
      prec +:= Ceiling(1/10*precNewton);
    else
      prec := Max([precstart,Min([precNewton,Ceiling(11/10*prec)]),Min([precNewton,Ceiling(-2*Log(err)/Log(10))])]);
      //prec := Min([precstart,Min([precNewton,Ceiling(11/10*prec)]),Min([precNewton,Ceiling(-2*Log(err)/Log(10))])]);
    end if;
    vprintf Shimura : "prec = %o\n", prec;
    // update solvec
    equations_eval := [Evaluate(eqn, Eltseq(solvec)) : eqn in equations]; // SeqEnum of evaluated equations
    J_eval := Evaluate(J, Eltseq(solvec)); // Jacobian evaluated
    if Ncols(J) eq Nrows(J) then
      Q, L := QLDecomposition(J_eval);
      solvec := solvec - Vector(equations_eval)*(L^-1)*Conjugate(Transpose(Q));
    else
      m := Nrows(J);
      n := Ncols(J);
      R0, Q0 := RQDecomposition(J_eval);
      R := Submatrix(R0,1,n-m+1,m,m); // get a square invertible matrix
      Q := Submatrix(Q0,n-m+1,1,m,n); // get a rectangular matrix with orthonormal rows (columns?)
      solvec := solvec - Vector(equations_eval)*Conjugate(Transpose(Q))*(R^-1);
      /*
      // NumericalSolution
      b := Vector(equations_eval)*Transpose(J_eval);
      // A := Transpose(J_eval)*J_eval;
      A := -J_eval*Transpose(J_eval);
      //y := NumericalSolution(A, b : Epsilon := err);
      y := NumericalSolution(A, b);
      solvec := solvec + y;
      */
    end if;
    // check if our solvec is good enough
    if prec ge precNewton and err lt 10^(-precNewton+Log(precNewton)) then
      vprintf Shimura : "Newton worked with precNewton = %o\n", precNewton;
      return Eltseq(solvec);
    end if;
  end for;
  // if we make it out then Newton didn't work
  error "Newton failed!";
end intrinsic;

intrinsic NewtonIterate(Gamma::GrpPSL2, precNewton::RngIntElt) -> GrpPSL2
  {uses equations and initial values assigned to Gamma.}
  // {Assigns start_vector [c4, c6, points0, points1, pointsoo, extra_points, lc, num_coeffs, den_coeffs] to Gamma.}
  equations := Gamma`TriangleNewtonEquations;
  start := Gamma`TriangleNewtonInitialization;
  sol := NewtonIterate(equations, start, precNewton);
  Gamma`TriangleNewtonSolution := sol;
  cfs_pts := sol; // coefficients including ramification points
  // get rid of ramification points: these might not be defined over K
  Gamma`TriangleNumericalCurveCoefficients := [cfs_pts[1], cfs_pts[2]];
  E := EllipticCurve([-27*cfs_pts[1],-54*cfs_pts[2]]);
  Gamma`TriangleNumericalCurveInvariants := jInvariant(E); // just a number...hmm
  points_offset := 2*(#Gamma`TriangleNewtonRamificationPoints0+#Gamma`TriangleNewtonRamificationPoints1+#Gamma`TriangleNewtonRamificationPointsoo);
  Gamma`TriangleNumericalBelyiMapLeadingCoefficient := cfs_pts[2+points_offset+1]; // lc
  num_vars := Gamma`TriangleNewtonVariablesNumeratorCoefficients;
  den_vars := Gamma`TriangleNewtonVariablesDenominatorCoefficients;
  Gamma`TriangleNumericalBelyiMapNumeratorCoefficients := [cfs_pts[2+points_offset+1+i] : i in [1..#num_vars]] cat [Parent(cfs_pts[1])!1]; // numerator
  Gamma`TriangleNumericalBelyiMapDenominatorCoefficients := [cfs_pts[2+points_offset+1+#num_vars+i] : i in [1..#den_vars]] cat [Parent(cfs_pts[1])!1]; // denominator
  return Gamma;
end intrinsic;

intrinsic NewtonHyperellipticRecognize(Gamma::GrpPSL2 : bound := 0) -> GrpPSL2
  {Recognize elements of solution (complex numbers) with power relations up to bound.}
  coeffs_list := [* *];
  cfs := Gamma`TriangleNewtonSolution;
  if bound eq 0 then // if bound is unassigned make it size of pointed passport
    sigma := Gamma`TriangleSigma;
    ppass := PassportRepresentatives(sigma : Pointed := true);
    bound := #ppass;
  end if;
  cfs_pts := cfs; // coefficients including ramification points
  // get rid of ramification points: these might not be defined over K
  cfs := [];
  cfs := [cfs_pts[1], cfs_pts[2]];
  points_offset := 2*(#Gamma`TriangleNewtonRamificationPoints0+#Gamma`TriangleNewtonRamificationPoints1+#Gamma`TriangleNewtonRamificationPointsoo);
  Append(~cfs, cfs_pts[2+points_offset+1]); // lc
  num_vars := Gamma`TriangleNewtonVariablesNumeratorCoefficients;
  den_vars := Gamma`TriangleNewtonVariablesDenominatorCoefficients;
  cfs cat:= [cfs_pts[2+points_offset+1+i] : i in [1..#num_vars]]; // numerator
  cfs cat:= [cfs_pts[2+points_offset+1+#num_vars+i] : i in [1..#den_vars]]; // denominator
  // bl is true if K is found
  bl := false;
  cfs := Reverse(cfs);
  // cfs := Reverse([u] cat phixden_seq cat phixnum_seq);
  m := bound;
  while ((not bl) and (m gt 0)) do
    cfs_ind := 0;
    while not bl and cfs_ind lt #cfs do
      cfs_ind +:= 1;
      bl, K, v, conj, uCC := MakeK(cfs[cfs_ind], m); // bound is m
    end while;
    m -:= 1;
  end while;
  if not bl then
    error "K not found; is the Galois orbit smaller than the passport size?  Try smaller m!";
  end if;
  for a in cfs do
    vprintf Shimura : "index cfs %o of %o\n", Index(cfs, a), #cfs;
    vprintf Shimura : "a = %o\n", a;
    vprintf Shimura : "recognize = %o\n", RecognizeOverK(a, K, v, conj);
    Append(~coeffs_list, RecognizeOverK(a, K, v, conj));
  end for;
  // assign to Gamma
  coeffs_list := Reverse(coeffs_list);
  //Gamma`TriangleNewtonSolutionExact := coeffs_list;
  Gamma`TriangleK := K;
  Gamma`TriangleKv := v;
  Gamma`TriangleKIsConjugated := conj;
  Gamma`TriangleKNumericalGenerator := uCC;
  // break up solution into parts
  // [c4, c6, points0, points1, pointsoo, lc, num_coeffs, den_coeffs, extra_points ]
  Gamma`TriangleExactCurveCoefficients := [coeffs_list[1], coeffs_list[2]];
  Gamma`TriangleExactBelyiMapLeadingCoefficient := coeffs_list[2+1];
  Gamma`TriangleExactBelyiMapNumeratorCoefficients := [coeffs_list[2+1+i] : i in [1..#num_vars]] cat [Parent(coeffs_list[1])!1]; // don't forget the leading term
  Gamma`TriangleExactBelyiMapDenominatorCoefficients := [coeffs_list[2+1+#num_vars+i] : i in [1..#den_vars]] cat [Parent(coeffs_list[1])!1]; // don't forget the leading term

  /*
  // [c4, c6, points0, points1, pointsoo, lc, num_coeffs, den_coeffs, extra_points ]
  Gamma`TriangleExactCurveCoefficients := [coeffs_list[1], coeffs_list[2]];
  points_offset := 2*(#Gamma`TriangleNewtonRamificationPoints0+#Gamma`TriangleNewtonRamificationPoints1+#Gamma`TriangleNewtonRamificationPointsoo);
  Gamma`TriangleExactBelyiMapLeadingCoefficient := coeffs_list[2+points_offset+1];
  num_vars := Gamma`TriangleNewtonVariablesNumeratorCoefficients;
  den_vars := Gamma`TriangleNewtonVariablesDenominatorCoefficients;
  Gamma`TriangleExactBelyiMapNumeratorCoefficients := [coeffs_list[2+points_offset+1+i] : i in [1..#num_vars]] cat [Parent(coeffs_list[1])!1]; // don't forget the leading term
  Gamma`TriangleExactBelyiMapDenominatorCoefficients := [coeffs_list[2+points_offset+1+#num_vars+i] : i in [1..#den_vars]] cat [Parent(coeffs_list[1])!1]; // don't forget the leading term
  */
  return Gamma;
end intrinsic;

// TODO
intrinsic NewtonHyperellipticMakeBelyiMaps(Gamma::GrpPSL2) -> GrpPSL2
  {Assigns Belyi curve and Belyi map to Gamma after some sanity checks.}
  sigma := Gamma`TriangleSigma;
  genus := Genus(Gamma);
  curve_coeffs := Gamma`TriangleExactCurveCoefficients;
  lc := Gamma`TriangleExactBelyiMapLeadingCoefficient;
  num_coeffs := Gamma`TriangleExactBelyiMapNumeratorCoefficients;
  denom_coeffs := Gamma`TriangleExactBelyiMapDenominatorCoefficients;
  K := Gamma`TriangleK;
  // curve_invs := Gamma`TriangleExactCurveInvariants; // only for genus 1
  c4, c6 := Explode(curve_coeffs);
  X := EllipticCurve([-27*c4, -54*c6]);
  //assert [[jInvariant(E)] : E in curve_list] eq curve_invs_exact;
  GenerateLSpaceBasis := function(n,KX);
    x := KX.1;
    y := KX.2;
    basis := [KX!1];
    for i in [2..n] do
      if i mod 2 eq 0 then
        Append(~basis,x^(i div 2));
      else //if i is odd
        Append(~basis, x^((i-3) div 2)*y);
      end if;
    end for;
    return basis;
  end function;
  // lc := leading_coeff[1];
  KX<x,y> := FunctionField(X);
  Xbasis := GenerateLSpaceBasis(Maximum(#num_coeffs, #denom_coeffs),KX);
  phi_denom := KX!0;
  for i in [1..#denom_coeffs] do
    phi_denom := phi_denom + (KX!denom_coeffs[i])*Xbasis[i];
  end for;
  phi_num := KX!0;
  for i in [1..#num_coeffs] do
    phi_num := phi_num - (KX!num_coeffs[i])*Xbasis[i];
  end for;
  phi := (KX!lc)*phi_num/phi_denom;
  sane := BelyiMapSanityCheck(Gamma`TriangleSigma, X, phi);
  // assign to Gamma
  Gamma`TriangleBelyiCurve := X;
  Gamma`TriangleBelyiMap := phi;
  if not sane then
    vprint Shimura : X, phi;
    error "FAILED SANITY CHECK!";
  end if;
  return Gamma;
end intrinsic;
