// ================================================================================
// Hyperelliptic
// ================================================================================

RemoveLeadingZeros := function(f,eps);
  fes := AbsEltseq(f);
  sf := Degree(LeadingTerm(f));
  while Abs(Coefficient(f,sf)) lt eps do
    fes[sf+1] := 0;
    sf +:= 1;
  end while;
  return Parent(f)!fes, sf;
end function;

RemoveLeadingZerosLaurent := function(f,eps);
  // returns error for machine zero series: leading term reaches precision threshold
  lc := LeadingCoefficient(f);
  while Abs(lc) lt eps do
    f := f - LeadingTerm(f);
    lc := LeadingCoefficient(f);
  end while;
  return f;
end function;

ZeroifyCoeffsLaurent := function(f,eps);
  f := RemoveLeadingZerosLaurent(f,eps);
  vf := Valuation(f);
  for i := vf to AbsolutePrecision(f)-1 do
    if Abs(Coefficient(f,i)) lt eps then
      f -:= Coefficient(f,i)*Parent(f).1^i;
    end if;
  end for;
  return f;
end function;

function ZeroifyCoeffs(coeffs, eps)
  assert Type(coeffs) eq SeqEnum;
  //assert #coeffs gt 0;
  CC := Parent(coeffs[1]);
  prec := Precision(CC);
  coeffs0 := [];
  for i in [1..#coeffs] do
    if Abs(coeffs[i]) lt eps then
      Append(~coeffs0, CC!0);
    else
      Append(~coeffs0, CC!coeffs[i]);
    end if;
  end for;
  return coeffs0;
end function;

function PolarPart(f)
  // Input: A Laurent series f
  // Output: The polar part of f, i.e., the Laurent tail of f
  new := f + BigO(Parent(f).1^0);
  new := ChangePrecision(new, Infinity());
  return new;
end function;

// should this really be an intrinsic?  Or should we just keep it as a function?
//function RiemannRochBasisHyperellipticCurveAnalytic(m, x_CC, y_CC, X_CC, Gamma)
intrinsic RiemannRochBasisHyperellipticAnalytic(m::RngIntElt, x_CC::RngSerLaurElt, y_CC::RngSerLaurElt, X_CC::Crv, Gamma::GrpPSL2Tri) -> Any
  {input: m integer, X_CC complex curve, x_CC, y_CC power series in w. output: basis for L(m*infty_1)}
  g := Genus(Gamma);
  // require g ge 2: "Only for genus >= 2";
  assert g ge 2;
  assert g eq Genus(X_CC);
  CCw<w> := Parent(x_CC);
  CC<I> := BaseRing(CCw);
  prec := Precision(CC);
  eps := 10^(-prec/2);
  Delta := ContainingTriangleGroup(Gamma);
  phi, kappa := TrianglePhi(Delta);
  basis := [Parent(y_CC)!1];
  // distinguish even and odd hyperelliptic cases
  if Valuation(y_CC) eq -(2*g+1) then // this is the odd case TODO test this case
    for i in [1..Floor(m/2)] do
      Append(~basis, x_CC^i);
    end for;
    if m ge 2*g+1 then
      for i in [0..Floor((m-(2*g+1))/2)] do
        Append(~basis, x_CC^i*y_CC); 
      end for;
    end if;
  elif Valuation(y_CC) eq -(g+1) then // this is the even case
    v,u := HyperellipticPolynomials(X_CC);
    Pow<xi> := LaurentSeriesRing(CC); // xi stands for x inverse, i.e., x^(-1)
    // TODO : Determine Precision to take...
    //Pow<t> := LaurentSeriesRing(CC : Precision := ???);
    vv := Evaluate(v,1/xi);
    uu := Evaluate(u,1/xi);
    yy := (1/2)*(-uu + Sqrt(uu^2 + 4*vv));
    // gt 0 or lt 0?
    if Re(LeadingCoefficient(y_CC)/LeadingCoefficient(yy)) gt 0 then
      //yy := -(1/2)*(-uu - Sqrt(uu^2 + 4*vv));
      yy := (1/2)*(-uu - Sqrt(uu^2 + 4*vv));
    end if;
    //printf "expansion for y = %o\n\n", yy; // printing
    for j in [g+1..m] do
      new := (xi^(-1))^(j-(g+1))*yy;
      new := PolarPart(new);
      //printf "for j = %o, polar part = %o\n", j, new;
      new := Evaluate(new,x_CC^(-1));
      new := x_CC^(j-(g+1))*y_CC - new;
      Append(~basis,new);
      //print basis; // printing
    end for;
  else
    error "what the heck? not even or odd?!?!";
  end if;
  return basis;
end intrinsic;
//end function;

intrinsic RiemannRochBasisHyperellipticExact(m::RngIntElt, X::CrvHyp) -> Any
  {}
  // input: m integer, X curve with algebraic coefficients
  // output: basis for L(m*infty_1)
  g := Genus(X);
  K := BaseRing(X);
  nu := K.1;
  KX<x,y> := FunctionField(X);
  v,u := HyperellipticPolynomials(X);
  basis := [KX!1];
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
    Pow<xi> := LaurentSeriesRing(K : Precision := 30); // xi stands for x inverse, i.e., x^(-1)
    // TODO : Determine Precision to take...
    //Pow<t> := LaurentSeriesRing(K : Precision := ???);
    vv := Evaluate(v,1/xi);
    uu := Evaluate(u,1/xi);
    yy := (1/2)*(-uu + Sqrt(uu^2 + 4*vv));
    // not sure if this is the right condition; see corresponding condition in analytic version.
    // want leading coeffs of y_CC and yy to have opposite sign.  I think that lc of y_CC is always -1
    if LeadingCoefficient(yy) ne 1 then
      yy := (1/2)*(-uu - Sqrt(uu^2 + 4*vv));
    end if;
    for j in [g+1..m] do
      new := (xi^(-1))^(j-(g+1))*yy;
      new := PolarPart(new);
      new := Evaluate(new,x^(-1));
      new := x^(j-(g+1))*y - new;
      Append(~basis,new);
    end for;
  else
    error "Not even or odd case...???";
  end if;
  return basis;
end intrinsic;

intrinsic TriangleHyperellipticTest(Sk::SeqEnum, Gamma::GrpPSL2Tri) -> Any
  {
  Test if a given Belyi map is hyperelliptic.
  Input: Sk, an echelonized basis for the space of wt k modular forms, given as the output of TrianglePoweSeriesBasis;
         Gamma, triangle subgroup
  Output: hyp_bool, a boolean, true if exactly one hyperelliptic relation is found;
          curve_coeffs, a SeqEnum containing the coefficients of the hyperelliptic relation found;
          curve_vals, a SeqEnum containing the valuations of the functions in the basis for the curve coefficients.
  }
  prec := Precision(BaseRing(Parent(Sk[1][1])));
  eps := 10^(-prec/2);
  g := Genus(Gamma);
  //require g ge 2: "Only for genus >= 2";
  assert g ge 2;
  Delta := ContainingTriangleGroup(Gamma);
  phi, kappa := TrianglePhi(Delta);

  vprint Shimura: "Creating series for coordinate functions x and y...";
  CCw<w> := Parent(Sk[1][1]);
  CC<I> := BaseRing(CCw);
  f1 := Sk[1][1];
  f2 := Sk[2][1];
  assert g eq #Sk;
  f_g := Sk[g][1];
  //make f1, f2, f_g series in w/kappa, just like phi
  f1 := Evaluate(f1, kappa*w);
  f2 := Evaluate(f2, kappa*w);
  f2 := RemoveLeadingZeros(f2, eps);
  f2 := f2/LeadingCoefficient(f2);
  f_g := Evaluate(f_g, kappa*w);
  f_g := RemoveLeadingZeros(f_g,eps);
  f_g := f_g/LeadingCoefficient(f_g);
  x_CC := f1/f2;
  y_CC := Derivative(x_CC)/f_g;
  vprint Shimura: "Computing curve...";
  vprintf Shimura: "\tForming matrix of series coefficients...\n";
  series := [x_CC^i : i in [0..2*g+2]] cat [x_CC^i*y_CC : i in [0..g+1]] cat [y_CC^2];
  curve_vals := [Valuation(h) : h in series];
  // 2*g + 3 + g + 2 + 1 = 3*g + 6 things in series
  //M := Matrix([[Coefficient(f, i) : i in [2*Valuation(y_CC)..(3*g+5 + 2*Valuation(y_CC))] ] : f in series]);
  // TODO: How many columns?  The + 10 is a hack.
  // M := Matrix([[Coefficient(f, i) : i in [2*Valuation(y_CC)..(3*g+5 + 2*Valuation(y_CC)+10)] ] : f in series]);
  M := Matrix([[Coefficient(f, i) : i in [2*Valuation(y_CC)..(3*g+5 + 2*Valuation(y_CC)+15)] ] : f in series]); // just for one example
  //do I need to worry about e, the order of the stabilizer?
  assert Ncols(M) ge Nrows(M);
  vprintf Shimura: "\tComputing numerical kernel...\n";
  kerX := NumericalKernel(M : Epsilon := eps);
  kerX := KSpaceWithBasis(kerX);
  vprintf Shimura : "Basis of kernel = %o\n", Basis(kerX);
  if Dimension(kerX) eq 0 then
    print "No hyperelliptic relation found!";
    hyp_bool := false;
    Gamma`TriangleIsHyperelliptic := hyp_bool;
    return hyp_bool, _, _;
  elif Dimension(kerX) eq 1 then
    print "Exactly one hyperelliptic relation found!";
    hyp_bool := true;
    kerX := Basis(kerX);
    kerX := Eltseq(kerX[1]);
    curve_coeffs := [kerX[i]/kerX[#kerX] : i in [1..#kerX]];
    curve_coeffs := ZeroifyCoeffs(curve_coeffs,eps);
    Gamma`TriangleIsHyperelliptic := hyp_bool;
    return hyp_bool, curve_coeffs, curve_vals;
  else
    // TODO maybe this should print kernel and dimension?
    error "Multiple hyperelliptic relations found! Try a higher precision.";
  end if;
end intrinsic;

// function TriangleHyperellipticNumericalCoefficients(Sk, Gamma)
intrinsic TriangleHyperellipticNumericalCoefficients(Sk::SeqEnum, Gamma::GrpPSL2Tri : curve_coeffs := [], curve_vals := []) -> Any
  {Input: Sk, an echelonized basis for the space of wt k modular forms, given as the output of TrianglePoweSeriesBasis; Gamma, triangle subgroup
  Output: Coefficients of the curve, numerator, and denominator of the Belyi map, sequences of valuations of elements of the basis used in computing
  curve, numerator, and denominator. All coefficients are assigned to Gamma.}

  prec := Precision(BaseRing(Parent(Sk[1][1])));
  eps := 10^(-prec/2);
  g := Genus(Gamma);
  //require g ge 2: "Only for genus >= 2";
  assert g ge 2;
  CCw<w> := Parent(Sk[1][1]);
  CC<I> := BaseRing(CCw);
  Delta := ContainingTriangleGroup(Gamma);
  phi, kappa := TrianglePhi(Delta);
  vprint Shimura: "Creating series for coordinate functions x and y...";
  f1 := Sk[1][1];
  f2 := Sk[2][1];
  assert g eq #Sk;
  f_g := Sk[g][1];
  //make f1, f2, f_g series in w/kappa, just like phi
  f1 := Evaluate(f1, kappa*w);
  f2 := Evaluate(f2, kappa*w);
  f2 := RemoveLeadingZeros(f2, eps);
  f2 := f2/LeadingCoefficient(f2);
  f_g := Evaluate(f_g, kappa*w);
  f_g := RemoveLeadingZeros(f_g,eps);
  f_g := f_g/LeadingCoefficient(f_g);
  x_CC := f1/f2;
  y_CC := Derivative(x_CC)/f_g;
  //printf "x_CC = %o\n", x_CC; // printing
  //printf "y_CC = %o\n\n", y_CC; // printing
  if #curve_coeffs eq 0 then // no pre-assigned curve_coeffs
    vprint Shimura: "Computing curve...";
    vprintf Shimura: "\tForming matrix of series coefficients...\n";
    series := [x_CC^i : i in [0..2*g+2]] cat [x_CC^i*y_CC : i in [0..g+1]] cat [y_CC^2];
    curve_vals := [Valuation(h) : h in series];
    // 2*g + 3 + g + 2 + 1 = 3*g + 6 things in series
    //M := Matrix([[Coefficient(f, i) : i in [2*Valuation(y_CC)..(3*g+5 + 2*Valuation(y_CC))] ] : f in series]);
    // TODO: How many columns?  The + 10 is a hack.
    M := Matrix([[Coefficient(f, i) : i in [2*Valuation(y_CC)..(3*g+5 + 2*Valuation(y_CC)+10)] ] : f in series]);
    //do I need to worry about e, the order of the stabilizer?
    assert Ncols(M) ge Nrows(M);
    //print Nrows(M), Ncols(M); // printing
    vprintf Shimura: "\tComputing numerical kernel...\n";
    kerX := NumericalKernel(M : Epsilon := eps);
    kerX := KSpaceWithBasis(kerX);
    assert Dimension(kerX) eq 1;
    curve_coeffs := Basis(kerX);
    //printf "curve_coeffs = %o\n", curve_coeffs; //printing
    curve_coeffs := Eltseq(curve_coeffs[1]);
    curve_coeffs := [curve_coeffs[i]/curve_coeffs[#curve_coeffs] : i in [1..#curve_coeffs]];
    curve_coeffs := ZeroifyCoeffs(curve_coeffs,eps);
    printf "curve_coeffs = %o\n", curve_coeffs;
    vprintf Shimura : "...curve found!\n";
  end if;

  CCt<t> := PolynomialRing(CC);
  u := CCt!0;
  v := CCt!0;
  for i in [0..2*g+2] do
    v -:= curve_coeffs[i+1]*t^i;
  end for;
  for i in [0..g+1] do
    u -:= curve_coeffs[2*g+4+i]*t^i;
  end for;
  X_CC := HyperellipticCurve(v,u);
  //printf "u = %o\n", u; // printing
  //printf "v = %o\n", v; // printing
  //printf "X_CC is %o\n\n", X_CC; // printing

  vprint Shimura: "Computing Belyi map...";  
  sigma := DefiningPermutation(Gamma);
  d := Degree(Parent(sigma[1]));
  cycs := CycleDecomposition(sigma[1]);
  s := #CycleDecomposition(sigma[1])[1];
  //t := g;
  t := d+g-s; //L2Riemann-Roch
  //t := 2*g-1-s+d; 
  //t := Ceiling((d-s)/(2*g-2) + 1);
  //t := Ceiling((d+g)/(2*g-2) - s);
  dim_bool := false;
  while (not dim_bool) and (t ge 0) do
    vprintf Shimura: "\tComputing Riemann-Roch spaces...\n";
    numbasis := RiemannRochBasisHyperellipticAnalytic(t, x_CC, y_CC, X_CC, Gamma);
    num_vals := [Valuation(h) : h in numbasis];
    denombasis := RiemannRochBasisHyperellipticAnalytic(s+t, x_CC, y_CC, X_CC, Gamma);
    denom_vals := [Valuation(h) : h in denombasis];
    printf "\ts = %o, t = %o\n", s, t; // printing
    a := DefiningABC(Gamma)[1];
    e := a div #CycleDecomposition(sigma[1])[1];
    printf "\te = %o\n", e; // printing

    vprintf Shimura: "\tForming matrix of series coefficients...\n";
    series := [f*phi : f in denombasis] cat numbasis;
    minval := Min([Valuation(f) : f in series]);
    printf "\tminval = %o\n", minval; // printing
    //M := Matrix([[Coefficient(f,e*n) : n in [minval..minval + #numbasis + #denombasis - 1]] : f in series]);
    M := Matrix([[Coefficient(f,e*n) : n in [minval..minval + #numbasis + #denombasis + 10]] : f in series]);
    printf "\tnrows = %o, ncols = %o\n", Nrows(M), Ncols(M); // printing
    vprint Shimura : "\tComputing numerical kernel...";
    kerphi := NumericalKernel(M : Epsilon := eps);
    kerphi := KSpaceWithBasis(kerphi);
    printf "\tdimension of kernel = %o\n", Dimension(kerphi);
    if Dimension(kerphi) eq 1 then
      dim_bool := true;
    elif Dimension(kerphi) eq 0 then
      error "Matrix had trivial kernel. Try a higher precision.";
    else
      printf "\tKernel dimension too large; reducing t\n\n";
      t := t - 1;
    end if;
  end while;
  assert Dimension(kerphi) eq 1;
  Gamma`TriangleRiemannRochParameters := [s,t];
  kerphi := Basis(kerphi);
  kerphi := Eltseq(kerphi[1]);
  kerphi := ZeroifyCoeffs(kerphi,eps);
  lc_ind := #kerphi;
  // find last nonzero coeff and divide through
  while (lc_ind ge 1) and (kerphi[lc_ind] eq 0) do
    lc_ind := lc_ind - 1;
  end while;
  //kerphi := [kerphi[i]/kerphi[#kerphi] : i in [1..#kerphi]];
  kerphi := [kerphi[i]/kerphi[lc_ind] : i in [1..#kerphi]];
  printf "map coeffs = %o\n", kerphi;
  vprintf Shimura : "...Belyi map found!\n";

  denom_coeffs := kerphi[1..#denombasis];
  num_coeffs := kerphi[#denombasis+1..#denombasis+#numbasis];
  while denom_coeffs[#denom_coeffs] eq 0 do
    Remove(~denom_coeffs,#denom_coeffs);
  end while;
  while num_coeffs[#num_coeffs] eq 0 do
    Remove(~num_coeffs,#num_coeffs);
  end while;
  printf "unscaled numerator coeffs = %o\n", num_coeffs;
  printf "unscaled denominator coeffs = %o\n", denom_coeffs;
  lambda, curve_coeffs, lc, num_coeffs, denom_coeffs := TriangleRescaleCoefficients(Gamma, [curve_coeffs, num_coeffs, denom_coeffs], [curve_vals, num_vals, denom_vals]);
  // write attributes for NewtonHyperelliptic
  Gamma`TriangleNewtonCoordinateSeries := [x_CC, y_CC];
  // write numerical attributes
  Gamma`TriangleNumericalCurveCoefficients := curve_coeffs;
  Gamma`TriangleNumericalBelyiMapLeadingCoefficient := lc;
  Gamma`TriangleNumericalBelyiMapNumeratorCoefficients := num_coeffs;
  Gamma`TriangleNumericalBelyiMapDenominatorCoefficients := denom_coeffs;
  Gamma`TriangleRescalingFactor := lambda;
  return Gamma, curve_coeffs, lc, num_coeffs, denom_coeffs, curve_vals, num_vals, denom_vals;
end intrinsic;
// end function;


// TODO deprecated below this...maybe delete?
// Also currently only works with maps defined over QQ; need Galois orbits
// Should probably move to galoisorbits.m with the other recognition code
  /*{
    Input: numerical coefficients for the hyperelliptic curve and the Belyi map given as output of TriangleHyperellipticNumericalCoefficients; lambda, rescaling factor
    Output: algebraic coefficients for the curve and Belyi map given as curve_coeffs_QQ, lc_QQ, num_coeffs_QQ, denom_coeffs_QQ;
  }*/
intrinsic TriangleHyperellipticExactCoefficients(curve_coeffs::SeqEnum, lc::FldComElt, num_coeffs::SeqEnum, denom_coeffs::SeqEnum) -> Any
  {
    Input: numerical coefficients for the hyperelliptic curve and the Belyi map given as output
    Output: algebraic coefficients for the curve and Belyi map given as curve_coeffs_QQ, lc_QQ, num_coeffs_QQ, denom_coeffs_QQ;
  }

  CC := Parent(curve_coeffs[1]);
  prec := Precision(CC);
  eps := 10^(-prec/2);
  K := RationalsAsNumberField();

  // recognize Belyi map coefficients
  curve_coeffs_QQ := [];
  for i in [1..#curve_coeffs] do
    if Abs(curve_coeffs[i]) lt eps then
      Append(~curve_coeffs_QQ, K!0);
    else
      Append(~curve_coeffs_QQ, Roots(PowerRelation(Re(curve_coeffs[i]),1),K)[1][1]);
    end if;
  end for;
  denom_coeffs_QQ := [];
  for i in [1..#denom_coeffs] do
    if Abs(denom_coeffs[i]) lt eps then
      Append(~denom_coeffs_QQ, K!0);
    else
      Append(~denom_coeffs_QQ, Roots(PowerRelation(Re(denom_coeffs[i]),1),K)[1][1]);
    end if;
  end for;
  num_coeffs_QQ := [];
  for i in [1..#num_coeffs] do
    if Abs(num_coeffs[i]) lt eps then
      Append(~num_coeffs_QQ, K!0);
    else
      Append(~num_coeffs_QQ, Roots(PowerRelation(Re(num_coeffs[i]),1),K)[1][1]);
    end if;
  end for;
  lc_QQ := Roots(PowerRelation(Re(lc),1),K)[1][1];

  return curve_coeffs_QQ, lc_QQ, num_coeffs_QQ, denom_coeffs_QQ;
end intrinsic;

//function TriangleHyperellipticBelyiMap(sigma, curve_coeffs_QQ, lc_QQ, num_coeffs_QQ, denom_coeffs_QQ)
intrinsic TriangleHyperellipticBelyiMap(sigma::SeqEnum[GrpPermElt], curve_coeffs_QQ::SeqEnum, lc_QQ::FldNumElt, num_coeffs_QQ::SeqEnum, denom_coeffs_QQ::SeqEnum) -> Any
  {
    Input: sigma, permutation triple, exact coefficients for the hyperelliptic curve and the Belyi map given as output of TriangleHyperellipticExactCoefficients
    Output: Hyperelliptic curve and Belyi map
  }

  Gamma := TriangleSubgroup(sigma);
  g := Genus(Gamma);
  d := Degree(Parent(sigma[1]));
  K := Parent(denom_coeffs_QQ[1]);

  // make curve
  Kt<t> := PolynomialRing(K);
  u := Kt!0;
  v := Kt!0;
  for i in [0..2*g+2] do
    v -:= curve_coeffs_QQ[i+1]*t^i;
  end for;
  for i in [0..g+1] do
    u -:= curve_coeffs_QQ[2*g+4+i]*t^i;
  end for;
  X := HyperellipticCurve(v,u);

  // make Belyi map
  KX<x,y> := FunctionField(X);
  s0 := #CycleDecomposition(sigma[1])[1];
  t0 := g; //Riemann-Roch
  //t0 := 2*g-1-s+d;
  //t0 := Ceiling((d-s0)/(2*g-2) + 1);
  //t0 := Ceiling((d+g)/(2*g-2) - s0);
  RR_basis := RiemannRochBasisHyperellipticExact(s0+t0,X);

  phiX_denom := KX!0;
  for i in [1..#denom_coeffs_QQ] do
    phiX_denom := phiX_denom + (KX!denom_coeffs_QQ[i])*RR_basis[i];
  end for;
  phiX_num := KX!0;
  for i in [1..#num_coeffs_QQ] do
    phiX_num := phiX_num - (KX!num_coeffs_QQ[i])*RR_basis[i];
  end for;
  phiX := (KX!lc_QQ)*phiX_num/phiX_denom;

  return X, phiX;
end intrinsic;
//end function;
