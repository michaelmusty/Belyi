declare verbose BelyiNewton, 1;

import "genusone.m" : NeedsExtra;

intrinsic GetAssignedAttributes(Gamma::GrpPSL2Tri) -> SeqEnum
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

/*
BEFORE NEWTONGALOISORBITS
intrinsic NewtonGenusOne(Gammas::SeqEnum[GrpPSL2Tri] : precstart := 40, precNewton := 1000, bound := 0) -> SeqEnum
  {NewtonGenusOne(Gamma) for Gamma in Gammas (loop over entire passport).}
  t0 := Cputime();
  for i := 1 to #Gammas do
    vprintf BelyiNewton : "%o of %o...\n", i, #Gammas;
    Gammas[i] := NewtonGenusOne(Gammas[i] : precstart := precstart, precNewton := precNewton, bound := bound);
  end for;
  t1 := Cputime();
  vprintf BelyiNewton : "DONE. That took %o seconds.\n", t1-t0;
  return Gammas;
end intrinsic;
*/

// NewtonGaloisOrbits
intrinsic NewtonGenusOne(Gammas::SeqEnum[GrpPSL2Tri] : precstart := 40, precNewton := 1000, bound := 0, PowserAl := "Arnoldi") -> GrpPSL2Tri
  {}
  SetVerbose("BelyiNewton", true); // temporarily don't print Shimura so we can see what's happening
  // SetVerbose("Shimura", false);
  vprintf BelyiNewton : "Let's compute a (genus one) Belyi map with Newton:\n";
  for i := 1 to #Gammas do // before Galois orbits
    Gamma := Gammas[i];
    // numerical data
      vprintf BelyiNewton : "Computing numerical data...";
      t0 := Cputime();
      Gamma := NewtonGetNumericalData(Gamma : prec := precstart, PowserAl := PowserAl);
      t1 := Cputime();
      vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
    // ramification points
      vprintf BelyiNewton : "Computing ramification points above 0,1,oo...";
      t0 := Cputime();
      Gamma := NewtonGetRamificationPoints(Gamma);
      t1 := Cputime();
      vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
    // generate equations
      vprintf BelyiNewton : "Computing (basic) Newton equations...";
      t0 := Cputime();
      Gamma := NewtonGetBasicEquations(Gamma);
      t1 := Cputime();
      vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
    // generate rescaling equation
      vprintf BelyiNewton : "Computing (rescaling) Newton equations...";
      t0 := Cputime();
      Gamma := NewtonGetRescalingEquation(Gamma);
      t1 := Cputime();
      vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
      Gamma`TriangleNewtonEquations := Gamma`TriangleNewtonBasicEquations cat [Gamma`TriangleNewtonRescalingEquation];
    // basic initialization values
      vprintf BelyiNewton : "Computing (basic) initialization values for Newton...";
      t0 := Cputime();
      Gamma := NewtonGetBasicInitializationValues(Gamma);
      t1 := Cputime();
      vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
    // Newton iteration
      vprintf BelyiNewton : "Computing Newton iterates...";
      t0 := Cputime();
      Gamma := NewtonIterate(Gamma, precNewton);
      t1 := Cputime();
      vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
  end for;
  // recognition
    vprintf BelyiNewton : "Recognizing algebraic numbers...";
    t0 := Cputime();
    if bound eq 0 then
      bound := #PassportRepresentatives(Gamma`TriangleSigma); // might not be the best?
    end if;
    TriangleRecognizeCoefficients(Gammas : ExactAl := "GaloisOrbits", DegreeBound := bound);
    // Gamma := NewtonRecognize(Gamma : bound := bound); // it's bound to be
    t1 := Cputime();
    vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
  // make Belyi maps
    vprintf BelyiNewton : "Making Belyi curves and maps...";
    t0 := Cputime();
    // Gamma := NewtonMakeBelyiMaps(Gamma);
    TriangleMakeBelyiMaps(Gammas);
    t1 := Cputime();
    vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
  // return
    return Gammas;
end intrinsic;

intrinsic NewtonGenusOne(Gamma::GrpPSL2Tri : precstart := 40, precNewton := 1000, bound := 0, PowserAl := "Arnoldi") -> GrpPSL2Tri
  {Less Naive wrapper...}
  SetVerbose("BelyiNewton", true); // temporarily don't print Shimura so we can see what's happening
  // SetVerbose("Shimura", false);
  vprintf BelyiNewton : "Let's compute a (genus one) Belyi map with Newton:\n";
  // numerical data
    vprintf BelyiNewton : "Computing numerical data...";
    t0 := Cputime();
    Gamma := NewtonGetNumericalData(Gamma : prec := precstart, PowserAl := PowserAl);
    t1 := Cputime();
    vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
  // ramification points
    vprintf BelyiNewton : "Computing ramification points above 0,1,oo...";
    t0 := Cputime();
    Gamma := NewtonGetRamificationPoints(Gamma);
    t1 := Cputime();
    vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
  // generate equations
    vprintf BelyiNewton : "Computing (basic) Newton equations...";
    t0 := Cputime();
    Gamma := NewtonGetBasicEquations(Gamma);
    t1 := Cputime();
    vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
  // generate rescaling equation
    vprintf BelyiNewton : "Computing (rescaling) Newton equations...";
    t0 := Cputime();
    Gamma := NewtonGetRescalingEquation(Gamma);
    t1 := Cputime();
    vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
    Gamma`TriangleNewtonEquations := Gamma`TriangleNewtonBasicEquations cat [Gamma`TriangleNewtonRescalingEquation];
  // basic initialization values
    vprintf BelyiNewton : "Computing (basic) initialization values for Newton...";
    t0 := Cputime();
    Gamma := NewtonGetBasicInitializationValues(Gamma);
    t1 := Cputime();
    vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
  // Newton iteration
    vprintf BelyiNewton : "Computing Newton iterates...";
    t0 := Cputime();
    Gamma := NewtonIterate(Gamma, precNewton);
    t1 := Cputime();
    vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
  // recognition
    vprintf BelyiNewton : "Recognizing algebraic numbers...";
    t0 := Cputime();
    if bound eq 0 then
      bound := #PassportRepresentatives(Gamma`TriangleSigma); // might not be the best?
    end if;
    Gamma := NewtonRecognize(Gamma : bound := bound); // it's bound to be
    t1 := Cputime();
    vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
  // make Belyi maps
    vprintf BelyiNewton : "Making Belyi curves and maps...";
    t0 := Cputime();
    Gamma := NewtonMakeBelyiMaps(Gamma);
    t1 := Cputime();
    vprintf BelyiNewton : "done. That took %o seconds.\n", t1-t0;
  // return
    return Gamma;
end intrinsic;

intrinsic NewtonGetNumericalData(Gamma::GrpPSL2Tri : prec := 40, PowserAl := "Arnoldi") -> GrpPSL2Tri
  {Computes numerical data necessary for Newton, writes it to Gamma and returns Gamma.}
  _:= UnitDisc(Gamma : Precision := prec);
  // this is what takes time
  ass_bool := assigned Gamma`TriangleNewtonSk and assigned Gamma`TriangleNewtonFD and assigned Gamma`TriangleUnitDisc;
  if not (ass_bool and (Gamma`TriangleUnitDisc)`prec ge prec) then
    Sk := PowerSeriesBasis(Gamma, 2 : prec := prec, Federalize := true, Al := PowserAl);
  else
    Sk := Gamma`TriangleNewtonSk;
  end if;
  coeffs, _, _, nonzero_inds, wts, coordinate_series := TriangleGenusOneNumericalBelyiMap(Sk[1], Gamma); // assigns coordinate series to Gamma
  // assign fundamental domain to Gamma
  DD := UnitDisc(Gamma : Precision := prec);
  FD := FundamentalDomain(Gamma, DD);
  Gamma`TriangleUnitDisc := DD;
  Gamma`TriangleNewtonFD := FD;
  Gamma`TriangleNewtonSk := Sk;
  return Gamma;
end intrinsic;

intrinsic NewtonGetRamificationPoints(Gamma::GrpPSL2Tri) -> GrpPSL2Tri
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
  inds := [];
  for i := 1 to 3 do
    cycs := sigma_cycs[i];
    pts_i := [];
    mults_i := [];
    inds_i := [];
    for cyc in cycs do
      Append(~mults_i, #cyc);
      ind := cyc[1];
      Append(~inds_i, ind);
      Append(~pts_i, FD[4*(ind-1)+i]);  // = alphas[ind]*V[i], V the Delta-FD
    end for;
    Append(~pts, pts_i);
    Append(~mults, mults_i);
    Append(~inds, inds_i);
  end for;
  pts := [pts[1], pts[3], pts[2]]; // now switch back to white, black, cross
  mults := [mults[1], mults[3], mults[2]];
  inds := [inds[1], inds[3], inds[2]];
  slots := [1, 3, 2]; // Delta-FD vertex slot for white, black, cross resp.
  // delete the point that maps to point at infinity
  Remove(~pts[1],1);
  Remove(~mults[1],1);
  Remove(~inds[1],1);
  // map points to the elliptic curve.  Each point is alphas[ind]*V[slot], so
  // its Abel-Jacobi value is computed exactly by walking the coset-graph
  // path from the identity to alphas[ind] chart by chart (the same
  // structure the period computation uses) -- no reduction and no
  // nearest-chart search needed
  pts_E := [];
  for i := 1 to 3 do
    pts_E_i := [];
    for j := 1 to #pts[i] do
      w_CC := TriangleCosetVertexToComplexPlane(inds[i][j], slots[i], Gamma, Sk);
      Append(~pts_E_i, TriangleAJToEllipticCurve(w_CC, Gamma, x, y));
    end for;
    Append(~pts_E, pts_E_i);
  end for;
  // assign points and multiplicities to Gamma
  Gamma`TriangleNewtonRamificationPoints0 := pts_E[1];
  Gamma`TriangleNewtonDiscRamificationPoints0 := pts[1];
  Gamma`TriangleNewtonRamificationMultiplicities0 := mults[1];
  Gamma`TriangleNewtonRamificationPoints1 := pts_E[2];
  Gamma`TriangleNewtonDiscRamificationPoints1 := pts[2];
  Gamma`TriangleNewtonRamificationMultiplicities1 := mults[2];
  Gamma`TriangleNewtonRamificationPointsoo := pts_E[3];
  Gamma`TriangleNewtonDiscRamificationPointsoo := pts[3];
  Gamma`TriangleNewtonRamificationMultiplicitiesoo := mults[3];
  return Gamma;
end intrinsic;

/*
intrinsic TwoTorsionTest(w::SpcHydElt, Gamma::GrpPSL2Tri, Sk::SeqEnum) -> Any
  {Given a point w in the hyperbolic disc associated to Gamma, test if w is a 2-torsion point of the associated elliptic curve.}
  assert Genus(Gamma) eq 1;
  Lambda := Gamma`TrianglePeriodLattice;
  test_list := Lambda;
  w_CC := TriangleDiscToComplexPlane(w, Gamma, Sk);
  prec := Precision(Parent(w_CC));
  Append(~test_list,2*w_CC);
  torsion_bool := true;
  // rel := LinearRelation(test_list); // this seems to give lots of false positives :( and takes forever
  rel, gud := IntegerRelation(test_list, 10^2); // this seems to give lots of false positives
  vprintf Shimura : "relation: %o\ngoodness of fit: %o\n", rel, gud;
  if gud lt 10^(-prec/2) then // it's probably gud
    vprintf Shimura : "%o is a 2-torsion point!\n", w;
    torsion_bool := true;
  else // not gud
    vprintf Shimura : "%o is (probably) not a 2-torsion point\n", w;
    torsion_bool := false;
  end if;
  return torsion_bool;
end intrinsic;
*/

intrinsic TwoTorsionTest(w::SpcHydElt, Gamma::GrpPSL2Tri, Sk::SeqEnum) -> Any
  {Given a point w in the hyperbolic disc associated to Gamma, test if w is a 2-torsion point of the associated elliptic curve.}
  assert Genus(Gamma) eq 1;
  Lambda := Gamma`TrianglePeriodLattice;
  test_list := Lambda;
  w_CC := TriangleDiscToComplexPlane(w, Gamma, Sk);
  Append(~test_list,2*w_CC);
  torsion_bool := true;
  try
    rel := LinearRelation(test_list); // this seems to give lots of false positives :(
    vprintf Shimura : "%o\n", rel;
    if (Max([Abs(el) : el in rel]) lt 10^2) and (Abs(rel[3]) eq 1) then // hack to the max...TODO: decide what a "small" linear relation is
      vprintf Shimura : "%o is a 2-torsion point!\n", w;
      torsion_bool := true;
    else
      vprintf Shimura : "%o is (probably) not a 2-torsion point\n", w;
      torsion_bool := false;
    end if;
  catch e
    torsion_bool := false;
    print "No linear relation found";
    printf "%o is not a 2-torsion point", w;
  end try;
  return torsion_bool;
end intrinsic;

intrinsic NewtonVanishingEquations(Gamma::GrpPSL2Tri) -> Any
  {}
  // setup
  white_vars := Gamma`TriangleNewtonVariables0;
  mults_white := Gamma`TriangleNewtonRamificationMultiplicities0;
  black_vars := Gamma`TriangleNewtonVariables1;
  mults_black := Gamma`TriangleNewtonRamificationMultiplicities1;
  cross_vars := Gamma`TriangleNewtonVariablesoo;
  mults_cross := Gamma`TriangleNewtonRamificationMultiplicitiesoo;
  inv_vars := Gamma`TriangleNewtonVariablesC4C6;
  lc_var := Gamma`TriangleNewtonVariablesLeadingCoefficient;
  num_vars := Gamma`TriangleNewtonVariablesNumeratorCoefficients;
  den_vars := Gamma`TriangleNewtonVariablesDenominatorCoefficients;
  Sk := Gamma`TriangleNewtonSk;
  d := Gamma`TriangleD;
  c4, c6 := Explode(inv_vars);
  R := Parent(c4);
  Rfrac := FieldOfFractions(R);
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
    if not TwoTorsionTest(w, Gamma, Sk) then // x-xp is local uniformizer t
      u := -y_p+y_p*Sqrt(1+(t^3+3*t^2*x_p+3*t*x_p^2+(-27*inv_vars[1])*t)/(y_p^2)); // plus or minus with sqrt...
      // numerator
      num := Ser!0;
      for i := 1 to #num_vars do // numerator monomials except leading term
        if i mod 2 eq 0 then
          num +:= num_vars[i]*(t+x_p)^(i/2);
        elif i eq 1 then
          num +:= num_vars[i];
        else // i>1 odd
          num +:= num_vars[i]*(t+x_p)^((i-3) div 2)*(u+y_p);
        end if;
      end for;
      if (#num_vars+1) eq 1 then // numerator just has constant term (which doesn't appear in num_vars)
        num +:= 1;
      elif (#num_vars+1) mod 2 eq 0 then // numerator leading term
        num +:= (t+x_p)^((#num_vars+1)/2);
      else
        num +:= (t+x_p)^((#num_vars+1-3) div 2)*(u+y_p);
      end if;
      // FIXME: should probably get rid of this---multiplying by lc change vanishing
      num *:= -lc_var; // negative because TriangleGenusOneNumericalBelyiMap outputs NEGATIVES of numerator coeffs
    else // y is local uniformizer t
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
    end if;
    phi0 := num;
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
    if not TwoTorsionTest(w, Gamma, Sk) then // x-xp is local uniformizer t
      u := -y_p+y_p*Sqrt(1+(t^3+3*t^2*x_p+3*t*x_p^2+(-27*inv_vars[1])*t)/(y_p^2)); // plus or minus with sqrt...
      // numerator
      num := Ser!0;
      for i := 1 to #num_vars do // numerator monomials except leading term
        if i mod 2 eq 0 then
          num +:= num_vars[i]*(t+x_p)^(i/2);
        elif i eq 1 then
          num +:= num_vars[i];
        else // i>1 odd
          num +:= num_vars[i]*(t+x_p)^((i-3) div 2)*(u+y_p);
        end if;
      end for;
      if (#num_vars+1) eq 1 then
        num +:= 1;
      elif (#num_vars+1) mod 2 eq 0 then // numerator leading term
        num +:= (t+x_p)^((#num_vars+1)/2);
      else
        num +:= (t+x_p)^((#num_vars+1-3) div 2)*(u+y_p);
      end if;
      num *:= -lc_var; // negative because TriangleGenusOneNumericalBelyiMap outputs NEGATIVES of numerator coeffs
      // denominator
      den := Ser!0;
      for i := 1 to #den_vars do // denominator monomials except leading term
        if i mod 2 eq 0 then
          den +:= den_vars[i]*(t+x_p)^(i/2);
        elif i eq 1 then
          den +:= den_vars[i];
        else // i>1 odd
          den +:= den_vars[i]*(t+x_p)^((i-3) div 2)*(u+y_p);
        end if;
      end for;
      if (#den_vars+1) eq 1 then
        den +:= 1; // Belyi map is polynomial
      elif (#den_vars+1) mod 2 eq 0 then // denominator leading term
        den +:= (t+x_p)^((#den_vars+1)/2);
      else
        den +:= (t+x_p)^((#den_vars+1-3) div 2)*(u+y_p);
      end if;
      // -lc(num)-(den)
    else // y is local uniformizer t
      // update ramification point: y-coordinate should be zero if 2-torsion
      Gamma`TriangleNewtonRamificationPoints1[k][2] := Parent(Gamma`TriangleNewtonRamificationPoints1[k][2])!0;
      Append(~equations, R!y_p);
      Rs<s> := PolynomialRing(Ser);
      f := s^3 + 3*x_p*s^2 + (3*x_p^2 - 27*c4)*s - t^2;
      fp := Derivative(f);
      s_is := [Ser!0];
      for i := 1 to d*mult do // hack
        new := s_is[i] - Evaluate(f,s_is[i])/Evaluate(fp,s_is[i]);
        Append(~s_is, Ser!new);
      end for;
      // both of these should give y^2 if the answer is right
      ss := s_is[#s_is];
      assert IsWeaklyEqual(ss^3 + 3*x_p*ss^2 + (3*x_p^2 - 27*c4)*ss, t^2);
      // numerator
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
      num *:= -lc_var; // negative because TriangleGenusOneNumericalBelyiMap outputs NEGATIVES of numerator coeffs
      // denominator
      den := Ser!0;
      for i := 1 to #den_vars do // denominator monomials except leading term
        if i mod 2 eq 0 then
          den +:= den_vars[i]*(ss+x_p)^(i/2);
        elif i eq 1 then
          den +:= den_vars[i];
        else // i>1 odd
          den +:= den_vars[i]*(ss+x_p)^((i-3) div 2)*(t+y_p);
        end if;
      end for;
      if (#den_vars+1) eq 1 then
        den +:= 1; // Belyi map is polynomial
      elif (#den_vars+1) mod 2 eq 0 then // denominator leading term
        den +:= (ss+x_p)^((#den_vars+1)/2);
      else
        den +:= (ss+x_p)^((#den_vars+1-3) div 2)*(t+y_p);
      end if;
    end if;
    // -lc(num)-(den)
    phi1 := num - den;
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
    if not TwoTorsionTest(w, Gamma, Sk) then // x-xp is local uniformizer t
      u := -y_p+y_p*Sqrt(1+(t^3+3*t^2*x_p+3*t*x_p^2+(-27*inv_vars[1])*t)/(y_p^2)); // negative?
      phioo := Ser!0;
      for i := 1 to #den_vars do // denominator monomials except leading term
        if i mod 2 eq 0 then
          phioo +:= den_vars[i]*(t+x_p)^(i/2);
        elif i eq 1 then
          phioo +:= den_vars[i];
        else // i>1 odd
          phioo +:= den_vars[i]*(t+x_p)^((i-3) div 2)*(u+y_p);
        end if;
      end for;
      if #den_vars+1 eq 1 then
        phioo +:= 1; // Belyi map is polynomial
      elif (#den_vars+1) mod 2 eq 0 then // denominator leading term
        phioo +:= (t+x_p)^((#den_vars+1)/2);
      else
        phioo +:= (t+x_p)^((#den_vars+1-3) div 2)*(u+y_p);
      end if;
    else // y is local uniformizer t
      // update ramification point: y-coordinate should be zero if 2-torsion
      Gamma`TriangleNewtonRamificationPointsoo[k][2] := Parent(Gamma`TriangleNewtonRamificationPointsoo[k][2])!0;
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
      den := Ser!0;
      for i := 1 to #den_vars do // denominator monomials except leading term
        if i mod 2 eq 0 then
          den +:= den_vars[i]*(ss+x_p)^(i/2);
        elif i eq 1 then
          den +:= den_vars[i];
        else // i>1 odd
          den +:= den_vars[i]*(ss+x_p)^((i-3) div 2)*(t+y_p);
        end if;
      end for;
      if (#den_vars+1) eq 1 then
        den +:= 1; // Belyi map is polynomial
      elif (#den_vars+1) mod 2 eq 0 then // denominator leading term
        den +:= (ss+x_p)^((#den_vars+1)/2);
      else
        den +:= (ss+x_p)^((#den_vars+1-3) div 2)*(t+y_p);
      end if;
      phioo := den;
    end if;
    for j := 0 to mults_cross[k]-1 do // vanish to order mults_cross[k]
      // Append(~equations, Rfrac!Coefficient(phioo, j));
      Append(~equations, R!Numerator(Rfrac!Coefficient(phioo, j)));
    end for;
  end for;
  return equations;
end intrinsic;

intrinsic NewtonGetBasicEquations(Gamma::GrpPSL2Tri) -> GrpPSL2Tri
  {Computes basic Newton equations (ramification, order of vanishing) and assigns them to Gamma.}
  // the s and the t
  sigma := Gamma`TriangleSigma;
  d := Gamma`TriangleD;
  s := #CycleDecomposition(sigma[1])[1];
  if s eq d then // TODO hack
    t := 0;
  else
    t := d-s+1;
  end if;
// number of points is also number of mults
// pull multiplicities from Gamma
  mults_white := Gamma`TriangleNewtonRamificationMultiplicities0;
  mults_black := Gamma`TriangleNewtonRamificationMultiplicities1;
  mults_cross := Gamma`TriangleNewtonRamificationMultiplicitiesoo;
  num_points := #mults_white+#mults_black+#mults_cross;
  num_coeffs_CC := Gamma`TriangleNumericalBelyiMapNumeratorCoefficients;
  den_coeffs_CC := Gamma`TriangleNumericalBelyiMapDenominatorCoefficients;
// generate polynomial ring
  var_names := ["c4", "c6"];
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
  // for i := 1 to t-1 do // assume numerator is monic, TODO what about when t is 1?!?!
  for i := 1 to #num_coeffs_CC-1 do // assume numerator is monic, TODO what about when t is 1?!?!
    if i eq 1 then
      Append(~var_names, Sprintf("a%o", 0));
    else
      Append(~var_names, Sprintf("a%o", i));
    end if;
  end for;
  // for i := 1 to s+t-1 do // assume denominator is monic (might not work if numerator or denominator happens to lie in a smaller L-space) try next line instead
  for i := 1 to #den_coeffs_CC-1 do // assume denominator is monic
    if i eq 1 then
      Append(~var_names, Sprintf("b%o", 0));
    else
      Append(~var_names, Sprintf("b%o", i));
    end if;
  end for;
  // make special point variables if we need to
  if NeedsExtra(Gamma) then
    Append(~var_names, "x_s");
    Append(~var_names, "y_s");
  end if;
// make R
  R := PolynomialRing(Rationals(), #var_names, "grevlex");
  AssignNames(~R, var_names);
  // make pairs for points variables cuz...jeez
  inv_vars := [R.1, R.2];
  white_vars := []; // pairs [x1_w, y1_w],...
  for i := 1 to #mults_white do
    x_ind := 1+2*i;
    y_ind := 2+2*i;
    Append(~white_vars, [R.x_ind, R.y_ind]);
  end for;
  black_vars := []; // pairs [x1_b, y1_b],...
  for i := 1 to #mults_black do
    x_ind := 1+2*#mults_white+2*i;
    y_ind := 2+2*#mults_white+2*i;
    Append(~black_vars, [R.x_ind, R.y_ind]);
  end for;
  cross_vars := [];
  for i := 1 to #mults_cross do
    x_ind := 1+2*#mults_white+2*#mults_black+2*i;
    y_ind := 2+2*#mults_white+2*#mults_black+2*i;
    Append(~cross_vars, [R.x_ind, R.y_ind]);
  end for;
  vprintf Shimura : "white vars = %o\n", white_vars;
  vprintf Shimura : "black vars = %o\n", black_vars;
  vprintf Shimura : "cross vars = %o\n", cross_vars;
  // make lists of variables for coefficients of Belyi map
  lc_ind := 2*(1+num_points)+1;
  lc_var := R.lc_ind;
  num_vars := [];
  for i := 1 to #num_coeffs_CC-1 do
    ind := 2*(1+num_points)+i+1;
    Append(~num_vars, R.ind);
  end for;
  vprintf Shimura : "R = %o\n", R;
  den_vars := [];
  // TODO what if t=1
  for i := 1 to #den_coeffs_CC-1 do
    ind := 2*(1+num_points)+1+#num_vars+i;
    Append(~den_vars, R.ind);
  end for;
  vprintf Shimura : "num vars = %o\n", num_vars;
  vprintf Shimura : "den vars = %o\n", den_vars;
  if NeedsExtra(Gamma) then
    special_vars := [];
    Append(~special_vars, R.(#var_names-1));
    Append(~special_vars, R.#var_names);
  end if;
  // make the equations
  equations := [];
  Rfrac := FieldOfFractions(R);
  // assign VARS to Gamma
  Gamma`TriangleNewtonVariablesC4C6 := inv_vars;
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
        Append(~equations, pt[2]^2-(pt[1]^3-27*inv_vars[1]*pt[1]-54*inv_vars[2]));
        i := i+1;
      end while;
    end for;
  print Parent(equations[1]); //printing
  // equations for ramification
  equations cat:= NewtonVanishingEquations(Gamma);
  /*
    Ser<t> := LaurentSeriesRing(Rfrac);
    // white equations
    for k := 1 to #white_vars do
      pt := white_vars[k];
      x_p := Ser!pt[1];
      y_p := Ser!pt[2];
      u := -y_p+y_p*Sqrt(1+(t^3+3*t^2*x_p+3*t*x_p^2+(-27*inv_vars[1])*t)/(y_p^2)); // plus or minus with sqrt...
      // numerator
      num := Ser!0;
      for i := 1 to #num_vars do // numerator monomials except leading term
        if i mod 2 eq 0 then
          num +:= num_vars[i]*(t+x_p)^(i/2);
        elif i eq 1 then
          num +:= num_vars[i];
        else // i>1 odd
          num +:= num_vars[i]*(t+x_p)^((i-3) div 2)*(u+y_p);
        end if;
      end for;
      if (#num_vars+1) eq 1 then // numerator just has constant term (which doesn't appear in num_vars)
        num +:= 1;
      elif (#num_vars+1) mod 2 eq 0 then // numerator leading term
        num +:= (t+x_p)^((#num_vars+1)/2);
      else
        num +:= (t+x_p)^((#num_vars+1-3) div 2)*(u+y_p);
      end if;
      num *:= -lc_var; // negative because TriangleGenusOneNumericalBelyiMap outputs NEGATIVES of numerator coeffs
      phi0 := num;
      for j := 0 to mults_white[k]-1 do // vanish to order mults_white[k]
        Append(~equations, R!Numerator(Rfrac!Coefficient(phi0, j)));
      end for;
    end for;
    // black equations: remember that TriangleGenusOneNumericalBelyiMap outputs NEGATIVES of numerator coeffs
    for k := 1 to #black_vars do
      pt := black_vars[k];
      x_p := Ser!pt[1];
      y_p := Ser!pt[2];
      u := -y_p+y_p*Sqrt(1+(t^3+3*t^2*x_p+3*t*x_p^2+(-27*inv_vars[1])*t)/(y_p^2)); // plus or minus with sqrt...
      // numerator
      num := Ser!0;
      for i := 1 to #num_vars do // numerator monomials except leading term
        if i mod 2 eq 0 then
          num +:= num_vars[i]*(t+x_p)^(i/2);
        elif i eq 1 then
          num +:= num_vars[i];
        else // i>1 odd
          num +:= num_vars[i]*(t+x_p)^((i-3) div 2)*(u+y_p);
        end if;
      end for;
      if (#num_vars+1) eq 1 then
        num +:= 1;
      elif (#num_vars+1) mod 2 eq 0 then // numerator leading term
        num +:= (t+x_p)^((#num_vars+1)/2);
      else
        num +:= (t+x_p)^((#num_vars+1-3) div 2)*(u+y_p);
      end if;
      num *:= -lc_var; // negative because TriangleGenusOneNumericalBelyiMap outputs NEGATIVES of numerator coeffs
      // denominator
      den := Ser!0;
      for i := 1 to #den_vars do // denominator monomials except leading term
        if i mod 2 eq 0 then
          den +:= den_vars[i]*(t+x_p)^(i/2);
        elif i eq 1 then
          den +:= den_vars[i];
        else // i>1 odd
          den +:= den_vars[i]*(t+x_p)^((i-3) div 2)*(u+y_p);
        end if;
      end for;
      if (#den_vars+1) eq 1 then
        den +:= 1; // Belyi map is polynomial
      elif (#den_vars+1) mod 2 eq 0 then // denominator leading term
        den +:= (t+x_p)^((#den_vars+1)/2);
      else
        den +:= (t+x_p)^((#den_vars+1-3) div 2)*(u+y_p);
      end if;
      // -lc(num)-(den)
      phi1 := num - den;
      for j := 0 to mults_black[k]-1 do // vanish to order mults_black[k]
        Append(~equations, R!Numerator(Rfrac!Coefficient(phi1, j)));
      end for;
    end for;
    // cross equations
    for k := 1 to #cross_vars do
      pt := cross_vars[k];
      x_p := Ser!pt[1];
      y_p := Ser!pt[2];
      u := -y_p+y_p*Sqrt(1+(t^3+3*t^2*x_p+3*t*x_p^2+(-27*inv_vars[1])*t)/(y_p^2)); // negative?
      phioo := Ser!0;
      for i := 1 to #den_vars do // denominator monomials except leading term
        if i mod 2 eq 0 then
          phioo +:= den_vars[i]*(t+x_p)^(i/2);
        elif i eq 1 then
          phioo +:= den_vars[i];
        else // i>1 odd
          phioo +:= den_vars[i]*(t+x_p)^((i-3) div 2)*(u+y_p);
        end if;
      end for;
      if #den_vars+1 eq 1 then
        phioo +:= 1; // Belyi map is polynomial
      elif (#den_vars+1) mod 2 eq 0 then // denominator leading term
        phioo +:= (t+x_p)^((#den_vars+1)/2);
      else
        phioo +:= (t+x_p)^((#den_vars+1-3) div 2)*(u+y_p);
      end if;
      for j := 0 to mults_cross[k]-1 do // vanish to order mults_cross[k]
        // Append(~equations, Rfrac!Coefficient(phioo, j));
        Append(~equations, R!Numerator(Rfrac!Coefficient(phioo, j)));
      end for;
    end for;
  */
  print Parent(equations[1]); //printing
  // special equations
  if NeedsExtra(Gamma) then
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
  // assign to Gamma
  if NeedsExtra(Gamma) then
    Gamma`TriangleNewtonVariablesSpecial := special_vars;
  end if;
  Gamma`TriangleNewtonBasicEquations := equations;
  return Gamma;
end intrinsic;

intrinsic NewtonGetBasicInitializationValues(Gamma::GrpPSL2Tri) -> GrpPSL2Tri
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
  c4, c6 := Explode(Gamma`TriangleNumericalCurveCoefficients);
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
  if NeedsExtra(Gamma) then
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
    vprintf Shimura : "Numerator equation :\n%o\n", phi_num;
    vprintf Shimura : "Denominator equation :\n%o\n", phi_den;
    // Locate the common zero P_s.
    //
    // P_s is a SIMPLE zero of den (den vanishes on D_oo + P_s), and by
    // Riemann-Roch it is the UNIQUE common zero of num and den.  So:
    // enumerate the zeros of den on the curve from the norm equation of den
    // (whose coefficients are accurate to working precision), Newton-refine
    // each as a 2x2 system (den, curve) -- both equations are simple at P_s,
    // so this converges quadratically with no cluster smearing -- and select
    // the unique refined zero where num also vanishes: at the true P_s the
    // relative num-residual is ~10^(-prec), at every other zero of den it is
    // bounded away by many orders of magnitude.
    //
    // Two approaches that do NOT work here, for the record:
    // (1) matching roots of the num norm equation against roots of the den
    //     norm equation (the original implementation): num may vanish at P_s
    //     to high order -- e.g. when the group law forces P_s onto a
    //     ramified fiber point, as happens whenever num is even -- and a
    //     zero of multiplicity m smears the numerical roots into a cluster
    //     of radius ~10^(-prec/m), far wider than any sensible tolerance;
    // (2) computing P_s = -Sum(D_0') = -Sum(D_oo) (Abel) by chord-and-
    //     tangent from the stored ramification points: those points are
    //     Newton SEEDS of limited accuracy, and the fiber sum inherits and
    //     amplifies their error.  The fiber sums are still computed below as
    //     a coarse structural diagnostic (verbose only).
    A := -27*c4;  // the curve is y^2 = x^3 + A*x + B
    B := -54*c6;
    epspair := 10^(-(prec div 2));
    epscheck := 10^(-(prec div 4));
    ecadd := function(P, Q)  // [] represents the origin O
      if #P eq 0 then return Q; end if;
      if #Q eq 0 then return P; end if;
      if Abs(P[1]-Q[1]) lt epspair then
        if Abs(P[2]+Q[2]) lt epspair then
          return [CC | ];  // Q = -P (includes doubling a 2-torsion point)
        end if;
        lam := (3*P[1]^2 + A)/(2*P[2]);  // tangent
      else
        lam := (Q[2]-P[2])/(Q[1]-P[1]);  // chord
      end if;
      x3 := lam^2 - P[1] - Q[1];
      return [CC | x3, lam*(P[1]-x3) - P[2]];
    end function;
    ecmul := function(m, P)  // double-and-add
      R := [CC | ]; Q := P; mm := m;
      while mm gt 0 do
        if mm mod 2 eq 1 then R := ecadd(R, Q); end if;
        Q := ecadd(Q, Q); mm := mm div 2;
      end while;
      return R;
    end function;
    ecsum := function(pts, mults)
      S := [CC | ];
      for i := 1 to #pts do
        S := ecadd(S, ecmul(mults[i], [CC | pts[i][1], pts[i][2]]));
      end for;
      return S;
    end function;
    // diagnostic only: group-law fiber sums, at seed accuracy
    sum0 := ecsum(Gamma`TriangleNewtonRamificationPoints0,
                  Gamma`TriangleNewtonRamificationMultiplicities0);
    sumoo := ecsum(Gamma`TriangleNewtonRamificationPointsoo,
                   Gamma`TriangleNewtonRamificationMultiplicitiesoo);
    if #sum0 gt 0 then
      vprintf Shimura : "P_s from 0-fiber seeds (coarse)  = %o\n", [ComplexField(10) | sum0[1], -sum0[2]];
    end if;
    if #sumoo gt 0 then
      vprintf Shimura : "P_s from oo-fiber seeds (coarse) = %o\n", [ComplexField(10) | sumoo[1], -sumoo[2]];
    end if;
    // candidates: zeros of (den, curve), Newton-refined
    f := x^3 + A*x + B;
    fp := Derivative(f);
    d0 := Coefficient(phi_den, 0);
    d1 := Coefficient(phi_den, 1);
    d0p := Derivative(d0);
    d1p := Derivative(d1);
    abseval := function(pol, xa, ya)  // size of the terms of pol at (xa, ya)
      sc := RealField(prec)!0;
      for j := 0 to Degree(pol) do
        cj := Coefficient(pol, j);
        for i := 0 to Degree(cj) do
          sc +:= Abs(Coefficient(cj, i))*xa^i*ya^j;
        end for;
      end for;
      return sc;
    end function;
    refine := function(x0, y0)  // Newton on (den, curve); both simple at P_s
      xr := x0; yr := y0;
      for it := 1 to 8 do
        Fden := Evaluate(d0, xr) + Evaluate(d1, xr)*yr;
        Fcrv := yr^2 - Evaluate(f, xr);
        J11 := Evaluate(d0p, xr) + Evaluate(d1p, xr)*yr;
        J12 := Evaluate(d1, xr);
        J21 := -Evaluate(fp, xr);
        J22 := 2*yr;
        det := J11*J22 - J12*J21;
        if det eq 0 then break; end if;
        xr := xr - (J22*Fden - J12*Fcrv)/det;
        yr := yr - (-J21*Fden + J11*Fcrv)/det;
      end for;
      return [CC | xr, yr];
    end function;
    numres := function(P)  // relative residual of num at P
      return Abs(Evaluate(Evaluate(phi_num, P[2]), P[1]))
             / abseval(phi_num, Abs(P[1]), Abs(P[2]));
    end function;
    cands := [];
    for r in Roots(d0^2 - d1^2*f) do
      x0 := r[1];
      ycands := [CC | ];
      d1x := Evaluate(d1, x0);
      if d1x ne 0 then
        Append(~ycands, -Evaluate(d0, x0)/d1x);
      end if;
      ysqrt := Sqrt(Evaluate(f, x0));
      Append(~ycands, ysqrt);
      Append(~ycands, -ysqrt);
      for y0 in ycands do
        P := refine(x0, y0);
        Append(~cands, <numres(P), P[1], P[2]>);
      end for;
    end for;
    assert #cands gt 0;
    best := 1;
    for i := 2 to #cands do
      if cands[i][1] lt cands[best][1] then best := i; end if;
    end for;
    xs := cands[best][2];
    ys := cands[best][3];
    vprintf Shimura : "P_s selected = %o (relative num residual %o)\n",
      [ComplexField(10) | xs, ys], RealField(10)!cands[best][1];
    // P_s is the UNIQUE common zero of num and den (Riemann-Roch), so every
    // candidate at a genuinely different point must have num bounded away
    dsep := Max([RealField(prec) | 1, Abs(xs), Abs(ys)])*10^(-(prec div 8));
    for i := 1 to #cands do
      if Abs(cands[i][2]-xs) + Abs(cands[i][3]-ys) gt dsep then
        assert cands[i][1] gt epscheck;  // no second common zero
      end if;
    end for;
    if #sum0 gt 0 then
      vprintf Shimura : "distance of P_s from coarse 0-fiber estimate: %o\n",
        RealField(10)!(Abs(xs-sum0[1]) + Abs(ys+sum0[2]));
    end if;
    if #sumoo gt 0 then
      vprintf Shimura : "distance of P_s from coarse oo-fiber estimate: %o\n",
        RealField(10)!(Abs(xs-sumoo[1]) + Abs(ys+sumoo[2]));
    end if;
    // verify: P_s lies on the curve and is a zero of both num and den
    // (residuals measured relative to the size of the terms involved)
    eval_crv := Abs(ys^2 - (xs^3 + A*xs + B));
    scale_crv := Abs(ys)^2 + Abs(xs)^3 + Abs(A)*Abs(xs) + Abs(B);
    eval_num := Abs(Evaluate(Evaluate(phi_num,ys),xs));
    eval_den := Abs(Evaluate(Evaluate(phi_den,ys),xs));
    vprintf Shimura : "relative residual of curve equation at P_s: %o\n", RealField(10)!(eval_crv/scale_crv);
    vprintf Shimura : "relative residual of numerator at P_s: %o\n", RealField(10)!(eval_num/abseval(phi_num, Abs(xs), Abs(ys)));
    vprintf Shimura : "relative residual of denominator at P_s: %o\n", RealField(10)!(eval_den/abseval(phi_den, Abs(xs), Abs(ys)));
    assert eval_crv lt scale_crv*epscheck;
    assert eval_num lt abseval(phi_num, Abs(xs), Abs(ys))*epscheck;
    assert eval_den lt abseval(phi_den, Abs(xs), Abs(ys))*epscheck;
    vprintf Shimura : "Common zero = %o\n", [xs, ys];
    Gamma`TriangleNewtonInitializationSpecialPoint := [xs, ys];
  end if;
  // assign stuff to Gamma
  Gamma`TriangleNewtonInitializationC4 := c4;
  Gamma`TriangleNewtonInitializationC6 := c6;
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
  if NeedsExtra(Gamma) then
    start := [c4, c6] cat white cat black cat cross cat [lc] cat num cat den cat [xs, ys];
  else
    start := [c4, c6] cat white cat black cat cross cat [lc] cat num cat den;
  end if;
  Gamma`TriangleNewtonInitialization := start;
  return Gamma;
end intrinsic;

intrinsic NewtonGetRescalingEquation(Gamma::GrpPSL2Tri) -> GrpPSL2Tri
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

intrinsic NewtonIterate(Gamma::GrpPSL2Tri, precNewton::RngIntElt) -> GrpPSL2Tri
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

intrinsic NewtonRecognize(Gamma::GrpPSL2Tri : bound := 0) -> GrpPSL2Tri
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

intrinsic NewtonMakeBelyiMaps(Gamma::GrpPSL2Tri) -> GrpPSL2Tri
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
