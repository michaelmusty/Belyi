// Code to recognize algebraic coefficients by taking denominators into account

intrinsic IsGoodMinpoly(f,bad_primes)
  {Given a polynomial and a set of bad primes, check that f looks plausible as a minpoly. I.e., primes occurring in the discriminant that aren't supposed to be bad occur to even powers.}
  K<nu> := NumberField(f);
  OK := Integers(K); // or should we do disc of f? will ring of integers be hard to compute
  d := Discriminant(OK);
  facts, rest := TrialDivision(d);
  good := true;
  for pair in facts do
    if not pair[1] in bad_primes then // all primes that aren't expected to be bad should occur to even power
      if pair[2] mod 2 ne 0 then
        good := false;
      end if;
    end if;
  end for;
  if not IsSquare(rest[1]) then
    good := false;
  end if;
  if good then
    return true, f, [el[1] : el in facts];
  else
    return false;
end intrinsic;

intrinsic AdvancedRescalingFactor(f,ps)
  {}

  a := &*ps[1..3]; // hack
  D := LeadingCoefficient(f);
  e := Floor(Log(a,D));
  return D/(a^e);
end intrinsic;

intrinsic AdvancedRescaleCoefficients(Gamma, lambda)
  {Rescale coefficients of curve, numerator, and denominator by lambda (weighted by orders of vanishing at infinity).}

  curve_coeffs := Gamma`TriangleNumericalCurveCoefficients;
  curve_vals := Gamma`TriangleCurveValuations;
  num_coeffs := Gamma`TriangleNumericalBelyiMapNumeratorCoefficients ;
  num_vals := Gamma`TriangleBelyiMapNumeratorValuations ;
  denom_coeffs := Gamma`TriangleNumericalBelyiMapDenominatorCoefficients ;
  denom_vals := Gamma`TriangleBelyiMapDenominatorValuations ;

  M_c := Minimum(curve_vals);
  curve_coeffs := [curve_coeffs[i]*(lambda^curve_vals[i] - M_c) : i in [1..#curve_coeffs]];
  M_n := Minimum(num_vals);
  num_coeffs := [num_coeffs[i]*(lambda^num_vals[i] - M_n) : i in [1..#num_coeffs]];
  M_d := Minimum(denom_vals);
  denom_coeffs := [denom_coeffs[i]*(lambda^denom_vals[i] - M_d) : i in [1..#denom_coeffs]];

  return curve_coeffs, num_coeffs, denom_coeffs;
end intrinsic;
