intrinsic S3Action(tau::GrpPermElt, phi::FldFunFracSchElt) -> FldFunFracSchElt
  {}
  S := Sym(3);
  assert Parent(tau) eq S;
  if tau eq S!(1,2) then
    return 1-phi;
  elif tau eq S!(1,3) then
    return 1/phi;
  elif tau eq S!(2,3) then
    return phi/(phi-1);
  elif tau eq S!(1,2,3) then
    return 1-1/phi;
  elif tau eq S!(1,3,2) then
    return 1/(1-phi);
  else
    return phi;
  end if;
end intrinsic;

// sigma one at a time
intrinsic BelyiMap(sigma::SeqEnum[GrpPermElt] : prec := 0, Al := "Default", ExactAl := "AlgebraicNumbers", DegreeBound := 0, precNewton := 0, Federalize := true) -> Any, Any
  {Computes the Belyi curve X and Belyi map f associated to the permutation triple sigma. Same description as below.}

  chi := &+[1/Order(sigma_s) : sigma_s in sigma];
  if chi ge 1 then
    if chi gt 1 then
      X, phi := SphericalBelyiMap(sigma);
    elif chi eq 1 then
      X, phi := EuclideanBelyiMap(sigma);
    end if;
  
    if BelyiMapSanityCheck(sigma, X, phi) then
      vprint Shimura : "...verified!";
    	return X, phi;
    else
      vprint Shimura : X, phi;
      error "Failed sanity check, so the Belyi map is wrong.  This shouldn't happen.";
    end if;
  end if;  

  Gamma := TriangleSubgroup(sigma);

  return BelyiMap(Gamma : prec := prec, Al := Al, ExactAl := ExactAl, DegreeBound := DegreeBound, precNewton := precNewton, Federalize := Federalize);
end intrinsic;

// Gamma one at a time
intrinsic BelyiMap(Gamma::GrpPSL2Tri : prec := 0, Al := "Default", ExactAl := "AlgebraicNumbers", DegreeBound := 0, precNewton := 0, Federalize := true) -> Any, Any, Any
  {
    Computes the Belyi curve X and Belyi map f associated to the triangle subgroup Gamma.
    Currently only works for genera 0, 1.
    Optional parameters:
      prec to determine precision to work in
      m the size of the Galois orbit and
      Federalize to consider multiple neighborhoods around each point and
      Al, with possible values:
        Al := "RecognizeSeries" recognizes series over K, with linear algebra over K,
        Al := "ByRamification", computing the roots via ramification points,
        Al := "NumericalKernel", which computes the numerical kernel using multiplied power series expansions,
        Al := "Newton", which in genus zero (and now genus 1) computes an approximate solution and lifts it iteratively
        to precision precNewton, or
        Al := "Default", which does the best it can depending on the circumstances.
        NumAl := "NumericalKernel", which computes the numerical kernel using multiplied power series expansions,
        NumAl := "Newton", not implemented yet.
        ExactAl := "GaloisOrbits", which recognizes coefficients (using the entire Galois orbit) over the rationals,
        ExactAl := "AlgebraicNumbers", which uses MakeK to recognize coefficients over a number field.
  }

  d := IndexDegree(Gamma);

  if DegreeBound eq 0 then
    m0 := #PassportRepresentatives(DefiningPermutation(Gamma) : Pointed := true);
  else
    m0 := DegreeBound;
  end if;

  if prec eq 0 then
    // prec := 30+Round(Log(d))^2;  // wild guess
    prec := 30+5*(Genus(Gamma)+1)*d;  // completely made up
  end if;
  _:= UnitDisc(Gamma : Precision := prec);

  if Genus(Gamma) eq 0 then
    k := 0;
    while SkDimension(Gamma,k) lt 2 do
      k +:= 2;
    end while;
    Sk := PowerSeriesBasis(Gamma, k : dim := 2, Federalize := Federalize);
    if Al eq "Default" then
      Al := "Newton";
    end if;
    if Al eq "RecognizeSeries" then
      Skb := RecognizeSeries(Sk, Gamma : m := DegreeBound, KeepTheta := true);
      _ := TrianglePhiGenusZeroRecognizeSeries(Skb, Gamma);
    elif Al in ["ByRamification", "NumericalKernel", "Newton"] then
      if precNewton eq 0 then
        precNewton := 200*m0*Round(Log(d));
      end if;
      _ := TrianglePhiGenusZeroNumericalBelyiMap(Sk, Gamma : Al := Al, m := DegreeBound, precNewton := precNewton);
    else
      error "Al not recognized";
    end if;
  elif Genus(Gamma) eq 1 then
    // compute numerical data
    Sk := PowerSeriesBasis(Gamma, 2 : prec := prec, Federalize := Federalize);
    if Al eq "Default" then
      // Al := "NumericalKernel";
      Al := "Newton";
    end if;
    if Al eq "RecognizeSeries" then
      error "not implemented for genus 1.";
      /*
        Skb := RecognizeSeries(Sk, Gamma : m := m);
        _ := TriangleTheta(Sk, Gamma : Al := "Ratio");
        _ := RecognizeSeries(Sk[1], Skb, Gamma);  // put in correct inputs, etc.
      */
    elif Al eq "Newton" then
      if precNewton eq 0 then
        precNewton := 100*m0*Round(Log(d));
      end if;
      Gamma := NewtonGenusOne(Gamma : precstart := prec, precNewton := precNewton, bound := m0);
      // Gamma := NewtonGenusOne(Gamma : precstart := prec, precNewton := precNewton, bound := DegreeBound);
    elif Al eq "NumericalKernel" then
      // right now this is the only NumAl
      // these 3 lines assign all numerical data to Gamma
      _, i_j, num_bool_j := TriangleGenusOneNumericalBelyiMap(Sk[1],Gamma);
    else
      error "Al not recognized";
    end if;
    // recognition
    // for Newton this already occurs (see newton.m) :/
    if Al ne "Newton" then
      if ExactAl eq "GaloisOrbits" then
        error "Only computed numerical data for one Belyi map. Please enter entire passport to compute via Galois orbits.";
      elif ExactAl eq "AlgebraicNumbers" then
        // assign exact coefficients to Gamma
        TriangleRecognizeAlgebraicCoefficients(Gamma : DegreeBound := DegreeBound);
      else
        error "ExactAl not recognized...no pun intended.";
      end if;
      // make Belyi map and assign to Gamma
      // once the button is more uniform, maybe do this for all genera? i.e. put outside if statement
      TriangleMakeBelyiMap(Gamma);
    end if;
  elif Genus(Gamma) eq 2 then
    // compute numerical data
    Sk := PowerSeriesBasis(Gamma, 2 : prec := prec, Federalize := Federalize);
    if Al eq "Default" then
      Al := "NumericalKernel";
    end if;
    if Al eq "RecognizeSeries" then
      error "not implemented for genus 2.";
      /*
        Skb := RecognizeSeries(Sk, Gamma : m := m);
        _ := TriangleTheta(Sk, Gamma : Al := "Ratio");
        _ := RecognizeSeries(Sk[1], Skb, Gamma);  // put in correct inputs, etc.
      */
    elif Al eq "NumericalKernel" then
      // right now this is the only NumAl
      // these 3 lines assign all numerical data to Gamma
      TriangleHyperellipticNumericalCoefficients(Sk, Gamma);
    else
      error "Al not recognized";
    end if;
    // recognition
    if ExactAl eq "GaloisOrbits" then
      error "Only computed numerical data for one Belyi map. Please enter entire passport to compute via Galois orbits.";
    elif ExactAl eq "AlgebraicNumbers" then
      // assign exact coefficients to Gamma
      TriangleRecognizeAlgebraicCoefficients(Gamma : DegreeBound := DegreeBound);
    else
      error "ExactAl not recognized...no pun intended.";
    end if;
    // make Belyi map and assign to Gamma
    // once the button is more uniform, maybe do this for all genera? i.e., put outside if statement?
    TriangleMakeBelyiMap(Gamma);
  else
    vprint Shimura : "Testing if hyperelliptic...";
    Sk := PowerSeriesBasis(Gamma, 2 : prec := prec, Federalize := Federalize);
    hyp_bool, curve_coeffs, curve_vals := TriangleHyperellipticTest(Sk, Gamma);
    if hyp_bool then
      Gamma := TriangleHyperellipticNumericalCoefficients(Sk, Gamma : curve_coeffs := curve_coeffs, curve_vals := curve_vals);
      TriangleRecognizeAlgebraicCoefficients(Gamma : DegreeBound := m0);
      TriangleMakeBelyiMap(Gamma);
    else
      error "not implemented for nonhyperelliptic genus > 2.";
    end if;
  end if;

  vprint Shimura : "Belyi map computed!  Now verifying...";
  
  if BelyiMapSanityCheck(DefiningPermutation(Gamma), Gamma`TriangleBelyiCurve, Gamma`TriangleBelyiMap) then
    vprint Shimura : "...verified!";
  	return Gamma`TriangleBelyiCurve, Gamma`TriangleBelyiMap, Gamma;
  else
    error "Failed sanity check, so the Belyi map is wrong: probably a precision issue.";
  end if;
end intrinsic;

// sigmas (passport at a time)
intrinsic BelyiMap(sigmas::SeqEnum[SeqEnum[GrpPermElt]] : prec := 0, Al := "Default", ExactAl := "GaloisOrbits", DegreeBound := 0, precNewton := 0, Federalize := true) -> Any, Any
  {Computes the Belyi curve X and Belyi map f associated to the permutation triple sigma. Same description as below.}
  // assertions
  chi_list := [];
  for sigma in sigmas do
    chi := &+[1/Order(sigma_s) : sigma_s in sigma];
    Append(~chi_list, chi);
  end for;
  if #SequenceToSet(chi_list) ne 1 then
    error "All permutation triples should be same type (hyperbolic, Euclidean, spherical).";
  else
    chi := chi_list[1];
  end if;

  if chi ge 1 then
    error "not implemented yet.";
  end if;  

  // make Gammas
  // TODO optimize for bad abc?
  Gammas := [TriangleSubgroup(sigma) : sigma in sigmas];
  return BelyiMap(Gammas : prec := prec, Al := Al, ExactAl := ExactAl, DegreeBound := DegreeBound, precNewton := precNewton, Federalize := Federalize);
end intrinsic;

// Gammas (passport at a time)
intrinsic BelyiMap(Gammas::SeqEnum[GrpPSL2Tri] : prec := 0, Al := "Default", ExactAl := "GaloisOrbits", DegreeBound := 0, precNewton := 0, Federalize := true) -> Any, Any, Any
  {
    Computes the Belyi curves and Belyi maps associated to the triangle subgroups in Gammas.
    Optional parameters:
      prec to determine precision to work in
      m the size of the Galois orbit and
      Federalize to consider multiple neighborhoods around each point and
      Al, with possible values:
        Al := "RecognizeSeries" recognizes series over K, with linear algebra over K,
        Al := "ByRamification", computing the roots via ramification points,
        Al := "NumericalKernel", which computes the numerical kernel using multiplied power series expansions,
        Al := "Newton", which in genus zero computes an approximate solution and lifts it iteratively
        to precision precNewton, or
        Al := "Default", which does the best it can depending on the circumstances.
        // TODO implement genus 1
        NumAl := "NumericalKernel", which computes the numerical kernel using multiplied power series expansions,
        NumAl := "Newton", not implemented yet.
        ExactAl := "GaloisOrbits", which recognizes coefficients (using the entire Galois orbit) over the rationals,
        ExactAl := "AlgebraicNumbers", which uses MakeK to recognize coefficients over a number field.
  }

  d := IndexDegree(Gammas[1]);
  if DegreeBound eq 0 then
    m0 := #PassportRepresentatives(DefiningPermutation(Gammas[1]) : Pointed := true);
  else
    m0 := DegreeBound;
  end if;

  // precision
  if precNewton eq 0 then
    precNewton := 100*m0*Round(Log(d));
  end if;
  if prec eq 0 then
    prec := 30+5*(Genus(Gammas[1])+1)*d;  // completely made up
  end if;
  _ := UnitDisc(Gammas[1] : Precision := prec);

  // check if all Gamma have same genus
  if false in [Genus(Gammas[i]) eq Genus(Gammas[1]) : i in [1..#Gammas]] then
    error "All Gammas must have the same genus.";
  end if;

  if Genus(Gammas[1]) eq 0 then
    if ExactAl eq "GaloisOrbits" then
      ExactAl := "AlgebraicNumbers";
      vprintf Shimura : "Galois orbits not implemented for genus 0, recognizing algebraic numbers instead.\n";
    end if;
    for i := 1 to #Gammas do
      BelyiMap(Gammas[i] : Al := Al, prec := prec, precNewton := precNewton, DegreeBound := m0);
    end for;
  elif Genus(Gammas[1]) eq 1 then
    if Al eq "Default" then
      Al := "Newton";
    end if;
    if Al eq "Newton" then
      for i := 1 to #Gammas do
        BelyiMap(Gammas[i] : Al := "Newton", prec := prec, precNewton := precNewton, DegreeBound := m0);
      end for;
    else
      TriangleRecordCoefficients(Gammas : prec := prec);
      TriangleRecognizeCoefficients(Gammas : ExactAl := ExactAl, DegreeBound := DegreeBound);
      TriangleMakeBelyiMaps(Gammas);
    end if;
  elif Genus(Gammas[1]) eq 2 then
    // TODO implement arbitrary genus hyperelliptic see BelyiMap(Gamma)
    TriangleRecordCoefficients(Gammas : prec := prec);
    TriangleRecognizeCoefficients(Gammas : ExactAl := ExactAl, DegreeBound := DegreeBound);
    TriangleMakeBelyiMaps(Gammas);
  else
    error "Not implemented for genus greater than 2.";
  end if;
  return Gammas;
end intrinsic;

// Sanity check
intrinsic BelyiMapSanityCheck(sigma::SeqEnum[GrpPermElt], X::Crv, phi::FldFunFracSchElt : lax := false) -> Any
  {Does a basic check to see if the candidate is plausible. If lax is set to true, then work in the category of lax Belyi maps.}
  supp, ramdeg := Support(Divisor(phi));
  supp1, ramdeg1 := Support(Divisor(phi-1));
  // print ramdeg;
  // print ramdeg1;
  cyc := [];
  for i := 1 to 3 do
    if i eq 1 then
      cyci := Sort([<ramdeg[i], Degree(supp[i])> : i in [1..#supp] | ramdeg[i] gt 0]);
    elif i eq 2 then
      cyci := Sort([<ramdeg1[i], Degree(supp1[i])> : i in [1..#supp1] | ramdeg1[i] gt 0]);
    else
      cyci := Sort([<Abs(ramdeg[i]), Degree(supp[i])> : i in [1..#supp] | ramdeg[i] lt 0]);
    end if;
    // Clean up in case points split
    j := 1;
    while j lt #cyci do
      if cyci[j][1] eq cyci[j+1][1] then
        cyci := cyci[1..j-1] cat [<cyci[j][1], cyci[j][2]+cyci[j+1][2]>] cat cyci[j+2..#cyci];
      else
        j +:= 1;
      end if;
    end while;
    Append(~cyc, cyci);
  end for;
  map_structure := cyc;
  sigma_structure := [Sort(CycleStructure(s)) : s in sigma];
  if lax eq false then
    return (map_structure eq sigma_structure);
  else
    if map_structure eq sigma_structure then
      return true, Sym(3)!1;
    else
      lax_equivalent := false;
      lax_permutation := Sym(3)!1;
      for s in Sym(3) do
        lax_sigma := S3Action(s, sigma);
        lax_sigma_structure := [Sort(CycleStructure(t)) : t in lax_sigma];
        if map_structure eq lax_sigma_structure then
          lax_equivalent := true;
          lax_permutation := Sym(3)!s;
        end if;
      end for;
      return lax_equivalent, lax_permutation;
    end if;
  end if;
end intrinsic;

intrinsic BelyiMapSanityCheck(Gamma::GrpPSL2Tri) -> Any
  {Overloaded to take Gamma}
  assert assigned Gamma`TriangleSigma;
  assert assigned Gamma`TriangleBelyiCurve;
  assert assigned Gamma`TriangleBelyiMap;
  return BelyiMapSanityCheck(Gamma`TriangleSigma, Gamma`TriangleBelyiCurve, Gamma`TriangleBelyiMap);
end intrinsic;
