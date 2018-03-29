// ================================================================================
// Genus one
// ================================================================================

intrinsic PrincipalPeriods(w_is::Any) -> Any
  {Computes the principal periods for Gamma.}
  lambda := w_is;
  while #lambda ne 2 do
    rel := LinearRelation(lambda : Al := "LLL");
    vprintf Shimura: "rel = %o\n", rel;
    j := 1;
    while Abs(rel[j]) ne 1 do
      j := j+1;
    end while;
    vprintf Shimura: "#Lambda = %o, Removing entry %o\n", #lambda, j;
    Remove(~lambda, j);
    vprintf Shimura: "Lambda = %o\n", [ComplexField(6)!l : l in lambda];
  end while;
  return lambda;
end intrinsic;

intrinsic TriangleGenusOnePeriods(Sk1::SeqEnum[RngSerPowElt], Gamma::GrpPSL2) -> Any
  {Given series expansions (in the form of the output of TrianglePowerSeriesBasis) for holomorphic differential on Gamma, return a basis for the period lattice.}
  require Genus(Gamma) eq 1 : "Only for genus one";

  CC<I> := BaseRing(Parent(Sk1[1]));
  prec := Precision(CC);
  eps := 10^(-prec+2);

  DD := TriangleUnitDisc(Gamma : Precision := prec);
  Delta := ContainingTriangleGroup(Gamma);
  FD := FundamentalDomain(Delta, DD);
  ws := [FD[1], FD[3], FD[2]]; //w_a, w_b, w_c, vertices of fundamental domain of Delta in DD
  DDs := Gamma`TriangleDDs;
  centers := [ComplexValue(Center(D)) : D in DDs];
  for j in [1..#Sk1] do
    Sk1[j] := Sk1[j]*2*I*Im(centers[j]);
  end for;

  // deal with leading terms
  f := Sk1[1];
  s := Degree(LeadingTerm(f));
  while Abs(Coefficient(f,s)) lt eps do
    s +:= 1;
  end while;

  rho := Max([Abs(z) : z in FundamentalDomain(Delta, DD)]);
  Sk1int := [Integral(f) : f in Sk1];
  alphas := TriangleCosetRepresentatives(Gamma);
  whichcoset := Gamma`TriangleWhichCoset;

  // compute the period lattice

  // just take sidepairings that don't identify adjacent edges
  sidepairing := [];
  for s in Gamma`TriangleSidePairing do
    if s[2][1] ne s[3][1] then
      // uber-hack: exclude pairings along da^(pm 1) sides; these should be contractible
      if ((not s[2][2] in [Delta.1, Delta.1^(-1)]) and (not s[3][2] in [Delta.1, Delta.1^(-1)])) then
        Append(~sidepairing, s);
      end if;
    end if;
  end for;
  // maybe should also exclude sidepairings that identify da^(pm 1) sides: these should all produce contractible loops

  // Compute endpoints for integrals in the various neighborhoods
  // I think we can just use black dots...seems legit?
  black := ws[2];
  cross := ws[3];
  periods := [];

  for s in sidepairing do
    vprintf Shimura: "Computing path for sidepairing %o\n", s;
    side1 := s[2];
    side2 := s[3];

    // need to keep track of cosets as well as points in the paths:
    // that way we can call WhichCoset to determine the neighborhood

    // first path: from first vertex back to identity translate
    path1 := [];
 //   path1cross := [];
    coset_path1 := [];
    Append(~path1,alphas[side1[1]]*black);
//    Append(~path1cross,alphas[side1[1]]*cross);
    Append(~coset_path1,alphas[side1[1]]);
    seq1 := Eltseq(alphas[side1[1]]^(-1));
    alpha0 := alphas[side1[1]];
    for i in [1..#seq1] do
      alpha0 := alpha0*Delta.seq1[i];
      Append(~coset_path1,alpha0);
      pt_new := alpha0*black;
//      pt_new_cross := alpha0*cross;
      Append(~path1,pt_new);
//      Append(~path1cross,pt_new_cross);
    end for;

    // second path: from second vertex back to identity translate
    path2 := [];
//    path2cross := [];
    coset_path2 := [];
    Append(~path2,alphas[side2[1]]*black);
//    Append(~path2cross,alphas[side2[1]]*cross);
    Append(~coset_path2,alphas[side2[1]]);
    seq2 := Eltseq(alphas[side2[1]]^(-1));
    alpha0 := alphas[side2[1]];
    for i in [1..#seq2] do
      alpha0 := alpha0*Delta.seq2[i];
      Append(~coset_path2,alpha0);
      pt_new := alpha0*black;
 //     pt_new_cross := alpha0*cross;
      Append(~path2,pt_new);
//      Append(~path2cross, pt_new_cross);
    end for;
    
    // make sure paths link up
    assert coset_path1[#coset_path1] eq Gamma!1;
    assert coset_path2[#coset_path2] eq Gamma!1;
    assert Abs(path1[#path1] - path2[#path2]) lt 10^(-10); //machine zero
//    assert path1cross[#path1cross] eq path2cross[#path2cross];

    // concatenate to make 1 path
    Remove(~path2,#path2);
//    Remove(~path2cross,#path2cross);
    Remove(~coset_path2,#coset_path2);
    path := path1 cat Reverse(path2);
//    path_cross := path1cross cat Reverse(path2cross);
    coset_path := coset_path1 cat Reverse(coset_path2);
    nbhds_path := [whichcoset[Index(alphas,c)] : c in coset_path];

 //   for p in [path, path_cross] do
    for p in [path] do
      if p eq path then
        //vprintf Shimura: "Black dots\n";
      // elif p eq path_cross then
        // vprintf Shimura: "Crosses\n";
      end if;
      omega := 0;
      for i in [2..#p] do
        // Need to map the points to the new neighborhoods! DiscToPlane and the PlaneToDisc(DDs[i],)
        start_pt := PlaneToDisc(DDs[nbhds_path[i]], DiscToPlane(UpperHalfPlane(), p[i-1]));
        end_pt := PlaneToDisc(DDs[nbhds_path[i]], DiscToPlane(UpperHalfPlane(), p[i]));
        new_int := Evaluate(Sk1int[nbhds_path[i]], ComplexValue(end_pt)) - Evaluate(Sk1int[nbhds_path[i]], ComplexValue(start_pt));
        omega +:= new_int;
        //vprintf Shimura: "Integral in nbhd %o from %o to %o was %o\n", nbhds_path[i], ComplexField(6)!ComplexValue(p[i-1]), ComplexField(6)!ComplexValue(p[i]), ComplexField(6)!new_int;
        // this will display the points in DDs[1] always...but I guess that's easier for visualizing the path
      end for;
      //vprintf Shimura: "Total period from %o to %o was %o\n\n", ComplexField(6)!ComplexValue(p[1]), ComplexField(6)!ComplexValue(p[#p]), ComplexField(6)!omega;
      Append(~periods,omega);
    end for;
  end for;
  vprintf Shimura: "Found periods\n%o\n\n", periods;
  vprintf Shimura: "Now reducing to 2 periods...\n";

  Lambda := PrincipalPeriods(periods);
  Gamma`TrianglePeriodLattice := Lambda;
  //return periods;
  return Lambda;
end intrinsic;

intrinsic TriangleMakeLattice(Lambda::SeqEnum[FldComElt]) -> Any
  {Given a sequence Lambda of two complex numbers, return the lattice generated by them.}
  Lambda_RR := [];
  for el in Lambda do
    Append(~Lambda_RR, [Re(el), Im(el)]);
  end for;
  M := Matrix(Lambda_RR);
  L := Lattice(M);
  return L;
end intrinsic;

intrinsic TriangleDiscToComplexPlane(w::SpcHydElt, Gamma::GrpPSL2, Sk::SeqEnum) -> Any
  {Given an element w of the hyperbolic disc, outputs the corresponding point in the complex plane (mod the lattice Lambda).}
  
  assert Genus(Gamma) eq 1;
  prec := Precision(Parent(Sk[1][1]));
  Sk1 := Sk[1];
  CC<I> := BaseRing(Parent(Sk[1][1]));
  DDs := Gamma`TriangleDDs;
  DD := Parent(w);
  centers := [ComplexValue(Center(D)) : D in DDs];
  for j in [1..#Sk1] do
    Sk1[j] := Sk1[j]*2*I*Im(centers[j]);
  end for;
  Sk1int := [Integral(f) : f in Sk1];
  w_CC := Evaluate(Sk1int[1], ComplexValue(w)) - Evaluate(Sk1int[1], ComplexValue(DD!0)); // CC mod Lambda
  return w_CC;
end intrinsic;

intrinsic TriangleComplexPlaneToEllipticCurve(c::FldComElt, Gamma::GrpPSL2, x::RngSerLaurElt, y::RngSerLaurElt) -> Any
  {Given an element c of the complex plane, outputs the corresponding point on the elliptic curve associated to Gamma.}

  assert Genus(Gamma) eq 1;
  Lambda := Gamma`TrianglePeriodLattice;
  L := TriangleMakeLattice(Lambda);
  shorties := ShortestVectors(L);
  radius := Min([Length(el) : el in shorties]);
  thresh := 0.5*radius;
  if Abs(c) gt thresh then // c is outside the radius of convergence, so divide to move it inside
    //k := Ceiling(Log(2,Abs(c)/radius));
    k := Ceiling(Log(2,Abs(c)/thresh));
    c_div := c/2^k;
  else
    c_div := c;
    k := 0;
  end if;
  // map point to elliptic curve
  c_div_E := [Evaluate(x,c_div), Evaluate(y, c_div)];
  c4, c6 := Explode(Gamma`TriangleNumericalCurveCoefficients);
  E_CC := EllipticCurve([-27*c4, -54*c6]);
  // find appropriate point on elliptic curve
  pts := Points(E_CC, c_div_E[1]);
  if Re(Eltseq(pts[1])[2]/c_div_E[2]) gt 0 then // make sure sign of y coordinates match
    c_div_E_CC := pts[1];
  else
    c_div_E_CC := pts[2];
  end if;
  assert Re(Eltseq(c_div_E_CC)[2]/c_div_E[2]) gt 0;
  c_E := 2^k*c_div_E_CC;
  c_E := Eltseq(c_E);
  assert c_E[3] eq 1;
  c_E := c_E[1..2];
  return c_E;
end intrinsic;

intrinsic TriangleDiscToEllipticCurve(w::SpcHydElt, Gamma::GrpPSL2, Sk::SeqEnum, x::RngSerLaurElt, y::RngSerLaurElt) -> GenerateLSpaceBasisAnalytic
  {Given an element w of the hyperbolic disc, outputs the corresponding point on the elliptic curve associated to Gamma.}

  assert Genus(Gamma) eq 1;
  prec := Precision(Parent(Sk[1][1]));
  w_CC := TriangleDiscToComplexPlane(w, Gamma, Sk);
  if Abs(w_CC) lt 10^(-prec/2) then // TODO check that w_CC is not one of the other lattice points
    error "w_CC is a pole of wp!";
  else
    w_E := TriangleComplexPlaneToEllipticCurve(w_CC, Gamma, x, y);
  end if;
  return w_E;
end intrinsic;

/*
intrinsic TriangleDiscToEllipticCurve(w::SpcHydElt, Gamma::GrpPSL2, Sk::SeqEnum, x::RngSerLaurElt, y::RngSerLaurElt) -> Any
  {Given an element w of the hyperbolic disc, outputs the corresponding point on the elliptic curve associated to Gamma.}
  // TODO assertions
  assert Genus(Gamma) eq 1;
  prec := Precision(Parent(Sk[1][1]));
  Sk1 := Sk[1];
  CC<I> := BaseRing(Parent(Sk[1][1]));
  DDs := Gamma`TriangleDDs;
  DD := Parent(w);
  centers := [ComplexValue(Center(D)) : D in DDs];
  for j in [1..#Sk1] do
    Sk1[j] := Sk1[j]*2*I*Im(centers[j]);
  end for;
  Sk1int := [Integral(f) : f in Sk1];
  w_CC := Evaluate(Sk1int[1], ComplexValue(w)) - Evaluate(Sk1int[1], ComplexValue(DD!0)); // CC mod Lambda
  if Abs(w_CC) lt 10^(-prec/2) then // TODO check that w_CC is not one of the other lattice points
    error "w_CC is a pole of wp!";
  else
    w_E := [Evaluate(x,w_CC), Evaluate(y,w_CC)]; // pair of complex numbers satisfying the curve?
  end if;
  return w_E;
end intrinsic;
*/

xcoeffs := function(N,c4,c6);
  // Given c4 and c6 for elliptic curve, recursively compute coefficients for x
  // N is number of coefficients computed
  as := [Parent(c4)!1];
  for m in [2..N] do
  L := m-3; // Note index shifting: a_L is in as[L+3], e.g. a_{-1} is as[2]
    a_new := 0;
    for k in [1..(L+1)] do
      a_new := a_new + (L-k)*(k-2)*as[L-k+3]*as[k-2+3]; // a_{L-k}*a_{k-2}
    end for;
    a_new := (1/4)*a_new;
    minus := 0;
    for i in [0..(L+1)] do
      if i eq 0 then
        jinds := [1..(L+1)];
      else // if i ne 0
        jinds := [0..(L+2-i)];
      end if;
      for j in jinds do
        k := L+2 - (i+j);
        minus := minus + as[i-2+3]*as[j-2+3]*as[k-2+3]; // a_{i-2}*a_{j-2}*a_{k-2}
      end for;
    end for;
    a_new := a_new - minus;
    if L ge 2 then
      a_new := a_new + 27*c4*as[L-1]; // a_{L-4}
    end if;
    if L eq 4 then
      a_new := a_new + 54*c6;
    end if;
    a_new := a_new/(L+3);
    Append(~as, a_new);
  end for;
  return as;
end function;

intrinsic TriangleGenusOneEllipticCurve(Lambda::SeqEnum[FldComElt], Gamma::GrpPSL2 : Ncoeffs := 70) -> Any
  {Given a basis for the period lattice, compute c4, c6 (as elements of a precision field)
    and return series expansions for x and y (also with complex coefficients) such that
    y^2 = x^3 - 27*c4*x - 54*c6. Ncoeffs is an optional parameter specifying how many coefficients
    of x to compute; default 70.}

  tau := Lambda[1]/Lambda[2];
  if Im(tau) lt 0 then
    Lambda := Reverse(Lambda);
    tau := Lambda[1]/Lambda[2];
  end if;
  j := jInvariant(tau);
  // assign jInvariant to Gamma
  Gamma`TriangleNumericalCurveInvariants := j;

  CC<I> := Parent(Lambda[1]);
  prec := Precision(CC);
  eps := 10^(-prec+2);
  pi := Pi(CC);
  c4 := (2*pi/6/Lambda[2])^4*Eisenstein(4,tau);
  c6 := (2*pi/6/Lambda[2])^6*Eisenstein(6,tau);
  cs := xcoeffs(Ncoeffs,c4,c6);

  Pow<T> := PowerSeriesRing(CC);
  x := (Pow!cs)/Pow.1^2;
  y := Derivative(x)/2;
  return x, y, c4, c6, j;
end intrinsic;

intrinsic TriangleGenusOneNumericalBelyiMap(Sk1::SeqEnum[RngSerPowElt], Gamma::GrpPSL2 : Ncoeffs := 0, rescale_ind := 0, num_bool := false) -> Any
  {Given a series expansion for a weight 2 modular form for a triangle subgroup Gamma
  of genus 1, return a sequence containing [j,c4,c6], [ leading coefficient of the Belyi map,
  the coefficients of the numerator, and the coefficients of the denominator ],
  and assigns everything to Gamma.}

  // TODO wild guess for Ncoeffs
  if Ncoeffs eq 0 then
    Ncoeffs := 200;
  end if;

  require Genus(Gamma) eq 1 : "Only for genus 1 triangle subgroups";  
  Delta := ContainingTriangleGroup(Gamma);
  phi, kappa := TrianglePhi(Delta);
  CC<I> := BaseRing(Parent(Sk1[1]));
  PowCC := PowerSeriesRing(CC);
  a := DefiningABC(Gamma)[1];
  CC := Parent(kappa);
  prec := Precision(CC);

  sigma := DefiningPermutation(Gamma);
  d := Degree(Parent(sigma[1]));
  cycs := CycleDecomposition(sigma[1]);
  s := #CycleDecomposition(sigma[1])[1];
  t := d - s + 1;

  Lambda := TriangleGenusOnePeriods(Sk1, Gamma);
  vprint Shimura : "Computing elliptic functions...";
  // x,y,c4,c6,j := TriangleGenusOneEllipticCurve(Lambda, Gamma : Ncoeffs := 100); FIXME
  x,y,c4,c6,j := TriangleGenusOneEllipticCurve(Lambda, Gamma : Ncoeffs := Ncoeffs);
  x := Evaluate(x,kappa*Parent(x).1);
  y := Evaluate(y,kappa*Parent(x).1);

  vprint Shimura : "Composing power series...";    
  u := 2*I*Integral(Evaluate(Sk1[1],kappa*Parent(Sk1[1]).1));
  xu := Evaluate(x+O(Parent(x).1^prec),u+O(Parent(u).1^prec));
  yu := Evaluate(y+O(Parent(y).1^prec),u+O(Parent(u).1^prec));

  GenerateLSpaceBasisAnalytic := function(n);
    basis := [Parent(xu)!1];
    for i in [2..n] do
      if i mod 2 eq 0 then
        Append(~basis,xu^(i div 2));
      else //if i is odd
        Append(~basis, xu^((i-3) div 2)*yu);
      end if;
    end for;
    return basis;
  end function;

  numbasis := GenerateLSpaceBasisAnalytic(t);
  denombasis := GenerateLSpaceBasisAnalytic(s+t);
  numdim := #numbasis;
  denomdim := #denombasis;

  vprintf Shimura: "s = %o, t = %o\n", s, t; // printing
  e := a div #CycleDecomposition(sigma[1])[1];
  vprintf Shimura: "e = %o\n", e; // printing

  vprint Shimura : "Computing numerical kernel...";    
  series := [f*phi : f in denombasis] cat numbasis;
  minval := Min([Valuation(ser) : ser in series]);
  vprintf Shimura: "minval = %o\n", minval; // printing
  // TODO: how many columns?  The + 10 is a hack
  M := Matrix([[Coefficient(f,e*n) : n in [minval..minval+s+2*t-1+10]] : f in series]);
  // M := Matrix([[Coefficient(f,e*n) : n in [minval..minval+e*(numdim+denomdim-1)]] : f in series]);
  printf "nrows = %o, ncols = %o\n", Nrows(M), Ncols(M);

  DD := TriangleUnitDisc(Gamma);
  rho := Max([Abs(z) : z in FundamentalDomain(Delta, DD)]);
  // epsilon := Re(CC!10^(-Floor((9/10)*(prec + Ncols(M)*Log(10,rho)))));
  epsilon := 10^(-prec/2);
  k := NumericalKernel(M : Epsilon := epsilon);
  vprintf Shimura: "Dimension of kernel = %o\n", Dimension(KSpaceWithBasis(k));
  assert Dimension(KSpaceWithBasis(k)) eq 1;
  k := Eltseq(k[1]);

  // get rid of machine zeroes
  k_new := [];
  for el in k do                     
    if AbsoluteValue(el) gt epsilon then
      Append(~k_new,el);            
    else
      Append(~k_new,Parent(k[1])!0);
    end if;
  end for;
  k := k_new;

  denom_coeffs := k[1..s+t];
  num_coeffs := k[s+t+1..s+2*t];
  while denom_coeffs[#denom_coeffs] eq 0 do
    Remove(~denom_coeffs,#denom_coeffs);
  end while;
  while num_coeffs[#num_coeffs] eq 0 do
    Remove(~num_coeffs,#num_coeffs);
  end while;
  printf "Unscaled curve coefficients: c4 = %o, c6 = %o\n", c4, c6; // printing
  printf "Unscaled numerator coefficients: %o\n", num_coeffs;
  printf "Unscaled denominator coefficients: %o\n", denom_coeffs;
  vprint Shimura : "Looking for scaling factor lambda...\n";  
  curve_coeffs := [c6, c4, -1, 1];
  curve_vals := [0,-2,-6,-6];
  //denom_vals := [Valuation(f) : f in denombasis]; 
  denom_vals := [Valuation(f) div Valuation(u) : f in denombasis]; // hack: make sure this works
  denom_vals := denom_vals[1..#denom_coeffs];
  //num_vals := [Valuation(f) : f in numbasis];
  num_vals := [Valuation(f) div Valuation(u) : f in numbasis]; // hack: make sure this works
  num_vals := num_vals[1..#num_coeffs];
  vprint Shimura : "Rescaling coefficients...";
  lambda, curve_coeffs, lc, num_coeffs, denom_coeffs, nonzero_inds, wts := TriangleRescaleCoefficients(Gamma, [curve_coeffs, num_coeffs, denom_coeffs], [curve_vals, num_vals, denom_vals]);
  vprintf Shimura : "Rescaling factor lambda = %o\n", lambda;
  c6 := curve_coeffs[1];
  c4 := curve_coeffs[2];
  Gamma`TriangleNumericalCurveInvariants := j; // already assigned, but do it again
  Gamma`TriangleNumericalCurveCoefficients := [c4,c6];
  Gamma`TriangleNumericalBelyiMapLeadingCoefficient := lc;
  Gamma`TriangleNumericalBelyiMapNumeratorCoefficients := num_coeffs;
  Gamma`TriangleNumericalBelyiMapDenominatorCoefficients := denom_coeffs;
  Gamma`TriangleNumericalPrecision := prec;
  Gamma`TriangleRescalingFactor := lambda;
  // rescale x and y for Newton
  // we don't want these with kappa!
  x_newton := Evaluate(x,(1/kappa)*Parent(x).1);
  y_newton := Evaluate(y,(1/kappa)*Parent(x).1);
  x_newton := x_newton*lambda^2;
  y_newton := y_newton*lambda^3;
  assert Parent(x_newton) eq Parent(y_newton);
  Gamma`TriangleNewtonCoordinateSeries := [x_newton, y_newton];
  return [* [j,c4,c6], [* lc, num_coeffs, denom_coeffs *] *], rescale_ind, num_bool, nonzero_inds, wts, [x_newton, y_newton];
end intrinsic;

// Newton's method for genus 1
// Outline:
/*
1) Get a rough approximation for the curve, E, and Belyi map, phi (in terms of x and y),
by computing the curve and the map numerically at low precision

2) Find the ramification points of phi on E by using the images of the dots in the fundamental domain
under the Laurent series for x and y

3) For each of these points P with coordinates (x_P, y_P), let t_P = x - x_P be a uniformizer
for the local ring at P. (As long as P is not a 2-torsion point---in this case, can take t_P = y - y_P.)
Express phi as a power series in t_P.

4) Impose vanishing to the order specified by the permutation triple at each P.  If phi vanishes to order
r, then we set the coefficients of 1 to t^(r-1) equal to 0. Each coefficient is a polynomial in
c4, c6, and the coefficients of the Belyi map, so this yields the desired system of polynomial equations.
There are two other conditions, too: one on the normalization of x, and setting two adjacent coefficients
equal.  (The latter is similar to how we obtain the rescaling factor lambda.)

5) Apply Newton's method to this system of equations.

*/
