subysquar_poly := function(phi, ysquarsub);
  // this function takes as input phi, a polynomial in x and y,
  // which is in fact a rational function in x and y^2,
  // and returns as output what you get by substituting ysquarsub in for y^2
  mons := Monomials(phi);
  cfs := Coefficients(phi);
  phisub := Parent(phi)!0;
  _<x,y> := Parent(phi);
  ysquarsub := Evaluate(ysquarsub,[x,y]);
  for i := 1 to #mons do
    e := Exponents(mons[i]);
    assert e[2] mod 2 eq 0;
    phisub +:= cfs[i]*ysquarsub^(e[2] div 2)*x^e[1];
  end for;  
  return phisub;
end function;

subysquar := function(phi, ysquarsub);
  // this function takes as input phi, a *rational function* in x and y,
  // and plugs it into the poly version by numerator and denominator
  num := subysquar_poly(Numerator(phi), ysquarsub);
  den := subysquar_poly(Denominator(phi), ysquarsub);
  return num/den;
end function;



//===============================================================
//
//
// Functions for Algorithm 2.5.6
//
//
//================================================================

GetR := function(sigma, delta_type);
  // This function determines the rotation index r
  // which is the index of T(Gamma) in Gamma
  struc_a := CycleStructure(sigma[1]);
  struc_b := CycleStructure(sigma[2]);
  struc_c := CycleStructure(sigma[3]);

  R_a := Max([delta_type[1]/c[1] : c in struc_a]);
  R_b := Max([delta_type[2]/c[1] : c in struc_b]);
  R_c := Max([delta_type[3]/c[1] : c in struc_c]);
  size, revVertNum := Max([R_c, R_b, R_a]);
  return size;
end function;

DetermineVertOfMaxRotation:= function(sigma, delta_type);
  // This function determines whether a,b, or c is the vertex of maximal rotation
  // i.e. the vertex we rotate around to generate R(Gamma)
  struc_a := CycleStructure(sigma[1]);
  struc_b := CycleStructure(sigma[2]);
  struc_c := CycleStructure(sigma[3]);

  R_a := Max([delta_type[1]/c[1] : c in struc_a]);
  R_b := Max([delta_type[2]/c[1] : c in struc_b]);
  R_c := Max([delta_type[3]/c[1] : c in struc_c]);
  size, revVertNum := Max([R_c, R_b, R_a]);
  if revVertNum eq 1 then
    vertnumber := 3;
  elif revVertNum eq 2 then
    vertnumber := 2;
  else
    vertnumber := 1;
  end if;
  return vertnumber, size;
end function;

PreProcessingConjugation:= function(sigma, delta_type);
  // This function "preprocesses" a given triple sigma
  // so that 1 is the maximally fixed element
  // and so that c is the vertex of maximal rotation when possible
  //If the triple is of the cba = ID variety, it also applies inverses to make
  //it of the abc = ID variety that is standard for this algorithm
  P:= Parent(sigma[1]);
  abcIsID := (sigma[1]*sigma[2]*sigma[3] eq P!(1));
  if not abcIsID then
    sigma[1] := sigma[1]^(-1);
    sigma[2] := sigma[2]^(-1);
    sigma[3] := sigma[3]^(-1);
  end if;      
  deg := Degree(Parent(sigma[1]));
  S := Sym(deg);
  sigma := [S!sigma[1], S!sigma[2], S!sigma[3]];
  vertnumber, size := DetermineVertOfMaxRotation(sigma, delta_type);
  cycleDecomp := CycleDecomposition(sigma[vertnumber]);
  min, pos := Min([#cycle : cycle in cycleDecomp]);
  swapForOne := cycleDecomp[pos][1];
  if swapForOne ne 1 then
    conjugator := Parent(sigma[vertnumber])!(1, swapForOne);
    newSigma_a := conjugator*sigma[1]*conjugator;
    newSigma_b := conjugator*sigma[2]*conjugator;
    newSigma_c := conjugator*sigma[3]*conjugator;
    newSigma := [newSigma_a, newSigma_b, newSigma_c];
  else
    newSigma := sigma;
  end if;
  if delta_type eq [3,3,3] then
    thingForVertC := newSigma[vertnumber];
    thingForVertVertNumber := newSigma[3];
    newSigma[3]:= thingForVertC;
    newSigma[vertnumber]:= thingForVertVertNumber;
    vertnumber:= 3;
  end if;
  return newSigma, vertnumber, size;
end function; 

//===============================================================
//
//
// Functions for Algorithm 2.4.4
//
//
//================================================================

GetV:=function(sigma, delta_type);
  //This function finds a spanning set for the translation group T(Gamma)
  //Coordinates are given relative to the standard basis for T(Delta)
  sigma_a := sigma[1];
  sigma_b := sigma[2];
  sigma_c := sigma[3];

  if delta_type eq [3,3,3] then
    sigma_1 := sigma_c^2*sigma_b^2*sigma_c^2*sigma_b*sigma_c^2;
    sigma_2 := sigma_b*sigma_c^2;
  elif delta_type eq [2,4,4] then
    sigma_1 := sigma_a*sigma_c^2;
    sigma_2 := sigma_b^3*sigma_c;
  else
    sigma_1 := sigma_c^4*sigma_b*sigma_a*sigma_c^3*sigma_a*sigma_c^3;
    sigma_2 := sigma_a*sigma_c^3;
  end if;

  c_1 := Cycle(sigma_1, 1);
  c_2 := Cycle(sigma_2^-1, 1);
  ell_1 := #c_1;
  ell_2 := #c_2;

  V := [[n1,n2] : n1 in [0..ell_1-1], n2 in [0..ell_2-1] | c_1[n1 + 1] eq c_2[n2 + 1]];
  V cat:=[[ell_1,0],[0, ell_2]];
  return V;
end function;

GetBasis := function(presigma, delta_type);
  //This function finds a basis for the translation group T(Gamma)
  //Coordinates are given relative to the basis for T(Delta)
  sigma, vertnumber, size := PreProcessingConjugation(presigma, delta_type);
  V := GetV(sigma, delta_type);
  M := Matrix(V);
  M0 := EchelonForm(M);
  t1 := M0[1];
  t2 := M0[2];
  t  := [t1,t2];
  return t;
end function;

GetN := function(presigma, delta_type);
  // This function calculates the index of T(Gamma) in T(Delta)
  sigma, vertnumber, r := PreProcessingConjugation(presigma, delta_type);
  P := Parent(sigma[1]);
  abcIsID := (sigma[1]*sigma[2]*sigma[3] eq P!(1));
  M := Matrix(GetBasis(sigma, delta_type));
  N := AbsoluteValue(Determinant(M));
    // JV: this is overkill for many purposes, we only need to work with the lcm!
  //N := Lcm(M[1,1],M[2,2]);
  return N, AbsoluteValue(Determinant(M));
end function;

Getg := function(presigma, delta_type);
  sigma, vertnumber, r := PreProcessingConjugation(presigma, delta_type);
  P := Parent(sigma[1]);
  abcIsID := (sigma[1]*sigma[2]*sigma[3] eq P!(1));
  M := Matrix(GetBasis(sigma, delta_type));
  g := Gcd(M[1,1],M[2,2]);
  return g;
end function;

//===============================================================
//
//
// Functions shared by kernel polynomial algorithms
//
//
//================================================================

PickKernelWithDistinctXs := function(presigma, delta_type);
  // This function returns points in the kernel of the map from C mod T(Delta) to C mod T(Gamma)
  // whose images on E(Delta) have distinct x-coordinates
  sigma, vertnumber, r := PreProcessingConjugation(presigma, delta_type);

  basis:= GetBasis(sigma, delta_type);
  n1 := basis[1][1];
  n2 := basis[1][2];
  m2 := basis[2][2];
  lattice := [ [a,b] : a in [0..m2], b in [0..n1]];
  lattice := Sort(lattice);
  cutoff := Ceiling(#lattice/2);
  coors := [lattice[n]: n in [1..cutoff]];
  firstRowFirstHalf := [[0,x] : x in [0..Floor((n1-1)/2)] ];
  lastColumn := [[x, n1] : x in [0..m2]];
  cuts := firstRowFirstHalf cat lastColumn;
  for cut in cuts do
     Exclude(~coors, cut);
  end for;
  KernelRelativeToStandardBasis := [[p[1]*n1, p[1]*n2 + p[2]*m2] : p in coors];
  _, N := GetN(presigma, delta_type);
  scaledKer := [[(1/N)*p[1], (1/N)*p[2]]: p in KernelRelativeToStandardBasis];
  Exclude(~scaledKer, [0,0]);
  return scaledKer;
end function;

GetDistinctXs := function(presigma, delta_type, prec);
  // This function determines the distinct x-coordinates
  // of points in the kernel of the isogeny from E(Delta) to E(Gamma)
  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    E := EllipticCurve([0,1]);
  else
    E := EllipticCurve([-1,0]);
  end if;

  preimage := PickKernelWithDistinctXs(presigma, delta_type);
  xs := [EllipticExponential(E,p : Precision := prec)[1] : p in preimage];
  return xs;
end function;

FindComplexRoots := function(presigma, delta_type, prec);
  // This function gets the roots of the kernel polynomial determining the isogeny psi
  // as complex numbers up to a given precision
  // sigma, vertnumber, r := PreProcessingConjugation(presigma, delta_type);
  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    E := EllipticCurve([0,1]);
  else
    E := EllipticCurve([-1,0]);
  end if;
  ComplexRoots := GetDistinctXs(presigma, delta_type, prec);
  return ComplexRoots;
end function;

ChooseDivisionPolyFactors := function(presigma, delta_type, prec);
  // This function factors the Nth division polynomial and
  // selects factors that contain the roots of our kernel polynomial
  comproots:= FindComplexRoots(presigma, delta_type, prec);
  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    E := EllipticCurve([0,1]);
  else
    E := EllipticCurve([-1,0]);
  end if;
  N := GetN(presigma, delta_type);
  phiN := DivisionPolynomial(E, N);
  factorList:=Factorization(phiN);
  factors := [entry[1]: entry in factorList];
  factorsToKeep := [ ];
  if (#comproots ge 1 and #factors ge 1) then
    for root in comproots do
      plugIns := [AbsoluteValue(Evaluate(g, root)) : g in factors];
      minVal, index := Minimum(plugIns);
      match := factors[index];
      //if Degree(match) ge 2 then
        Append(~factorsToKeep, match);
      //end if;
    end for;
  end if;
  facsNoRepeats := Set(factorsToKeep);
  list := [g : g in facsNoRepeats];
  return list;
end function;



//===============================================================
//
//
// Revised versions of functions in previous section to accomodate g scaling
//
//
//===============================================================

WPickKernelWithDistinctXs := function(presigma, delta_type,g);
  // This function returns points in the kernel of the map from C mod T(Delta) to C mod T(Gamma)
  // whose images on E(Delta) have distinct x-coordinates
  sigma, vertnumber, r := PreProcessingConjugation(presigma, delta_type);

  basis:= GetBasis(sigma, delta_type);
  n1 := basis[1][1]/g;
  n2 := basis[1][2]/g;
  m2 := basis[2][2]/g;
  lattice := [ [a,b] : a in [0..m2], b in [0..n1]];
  lattice := Sort(lattice);
  cutoff := Ceiling(#lattice/2);
  coors := [lattice[n]: n in [1..cutoff]];
  firstRowFirstHalf := [[0,x] : x in [0..Floor((n1-1)/2)] ];
  lastColumn := [[x, n1] : x in [0..m2]];
  cuts := firstRowFirstHalf cat lastColumn;
  for cut in cuts do
     Exclude(~coors, cut);
  end for;
  KernelRelativeToStandardBasis := [[p[1]*n1, p[1]*n2 + p[2]*m2] : p in coors];
  _, N := GetN(presigma, delta_type);
  N := N/g^2;
  scaledKer := [[(1/N)*p[1], (1/N)*p[2]]: p in KernelRelativeToStandardBasis];
  Exclude(~scaledKer, [0,0]);
  return scaledKer;
end function;

WGetDistinctXs := function(presigma, delta_type, prec, g);
  // This function determines the distinct x-coordinates
  // of points in the kernel of the isogeny from E(Delta) to E(Gamma)
  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    E := EllipticCurve([0,1]);
  else
    E := EllipticCurve([-1,0]);
  end if;

  preimage := WPickKernelWithDistinctXs(presigma, delta_type, g);
  xs := [EllipticExponential(E,p : Precision := prec)[1] : p in preimage];
  return xs;
end function;

WFindComplexRoots := function(presigma, delta_type, prec, g);
  // This function gets the roots of the kernel polynomial determining the isogeny psi
  // as complex numbers up to a given precision
  // sigma, vertnumber, r := PreProcessingConjugation(presigma, delta_type);
  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    E := EllipticCurve([0,1]);
  else
    E := EllipticCurve([-1,0]);
  end if;
  ComplexRoots := WGetDistinctXs(presigma, delta_type, prec, g);
  return ComplexRoots;
end function;

//===============================================================
//
//
// Torsion kerpol algorithm
//
//
//================================================================

TorsionKerpol := function(sigma, delta_type, prec);
  // This function computes the kernel polynomial by finding its
  // roots algebraically as x-coordinates of torsion points on EDelta

  // Setup and step 1 in Algorithm 3.2.2

  N := GetN(sigma, delta_type);
  if N eq 1 then
    return 1;
  end if;

  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    E := EllipticCurve([0,1]);
    K := NumberField(Polynomial([1,1,1]));
  else
    E := EllipticCurve([-1,0]);
    K := NumberField(Polynomial([1,0,1]));
  end if;
  phiN := DivisionPolynomial(E, N);
  
  // Step 2 in Algorithm 3.2.2

  RQ := PolynomialRing(RationalField());
  remainingPoly:= phiN;
  divisors := Divisors(N);
  Exclude(~divisors, N);
  properDivisorDivpols := [DivisionPolynomial(E,m): m in divisors ];
  for pol in properDivisorDivpols do
    gcd := GreatestCommonDivisor(RQ!pol, RQ!remainingPoly);
    remainingPoly := RQ!(remainingPoly/gcd);
  end for;

  // Step 3 in Algorithm 3.2.2

  RK:=PolynomialRing(K);
  remainingPoly := RK!remainingPoly;
  factors := [pair[1] : pair in Factorization(remainingPoly)];
  orderedFactors := Sort(factors);

  // Choose a factor with rational coefficients if possible (to simplify field extensions)

  highestDegree := Degree(orderedFactors[#orderedFactors]);
  simplerCandidates := [ ];
  for factor in orderedFactors do
    if (Degree(factor) eq highestDegree) and (Coefficients(factor) subset Rationals()) then
      Append(~simplerCandidates, factor);
    end if;
  end for;

  if #simplerCandidates ge 1 then
    gN := simplerCandidates[#simplerCandidates];
  else
    gN := orderedFactors[#orderedFactors];
  end if;
  L1 := ext<K|gN>;
  RL1<x> := PolynomialRing(L1);

  // Finding the x-coordinate for a generator of E[N] as a Z[j] module

  gN := RL1!gN;
  if L1 eq K then
    bool, thetaX := HasRoot(gN);
  else
    thetaX := L1.1;
  end if;

  // Finding the y-coordinate of our generator and enlarging L to contain it

  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    extPol := RL1!(x^2 - (thetaX^3 + 1));
    if IsIrreducible(extPol) then
      L2 := ext<L1|extPol>;
    else
      L2 := L1;
    end if;
    RL2 := PolynomialRing(L2);
    extPol:=RL2!extPol;
    thetaY := Roots(extPol)[1][1];
  else
    extPol := RL1!(x^2 - (thetaX^3 - thetaX));
    if IsIrreducible(extPol) then
      L2 := ext<L1|extPol>;
    else
      L2 := L1;
    end if;
    RL2 := PolynomialRing(L2);
    extPol:=RL2!extPol;
    thetaY := Roots(extPol)[1][1];
  end if;

  // Generating E[N] by the action of Z[j]

  E := BaseChange(E, L2);
  genP := E![thetaX,thetaY];
  j := L2!K.1;
  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    jgenP := E![j*genP[1], genP[2]];
  else
    jgenP := E![-genP[1], j*genP[2]];
  end if;  
  aOrbit := [genP];
  for a in [2..N] do 
    Append(~aOrbit,aOrbit[#aOrbit] + genP); 
  end for;
  bjOrbit := [jgenP];
  for b in [2..N] do 
    Append(~bjOrbit,bjOrbit[#bjOrbit] + jgenP); 
  end for;
  orbitOfgenp := [p1 + p2 : p1 in aOrbit, p2 in bjOrbit];
  algRootCandidates := [p[1]:p in orbitOfgenp];

  // Step 4 in Algorithm 3.2.5

  compRoots := FindComplexRoots(sigma, delta_type, prec);

  // Step 5 in Algorithm 3.2.5

  v := InfinitePlaces(L2)[1];
  rootsInCC := [Evaluate(r, v : Precision := prec) : r in algRootCandidates];
  algRoots := [ ];
  if (#compRoots ge 1 and #rootsInCC ge 1) then
    for root in compRoots do
      rootsDif := [AbsoluteValue(root - CCroot) : CCroot in rootsInCC];
      minDiff, index := Minimum(rootsDif);
      match := algRootCandidates[index];
      Append(~algRoots, match);
    end for;
  end if;

  // Step 6 in Algorithm 3.2.5

  RK<xK> := PolynomialRing(L2);
  if #algRoots ge 1 then
    kerpol := &*[xK - root : root in algRoots];
  else
    kerpol := 1;
  end if;

  // Simplifying kerpol if possible

  if Type(kerpol) ne RngIntElt then
    if L2 eq Rationals() then
      K0 := L2;
    else
      K0:= sub<L2|Coefficients(kerpol)>;
    end if;
    kerpol0 := Polynomial(ChangeUniverse(Eltseq(kerpol), K0));
    if K0 eq Rationals() then
      K0op, m0op := OptimizedRepresentation(K0 : Ramification := [2,3] cat PrimeDivisors(N));
    else
      f0, K01seq := Polredabs(MinimalPolynomial(K0.1));
      K0op := NumberField(f0);
      m0op := hom<K0 -> K0op | K0op!K01seq>;
    end if;
    // K0op, m0op:=OptimizedRepresentation(K0 : Ramification := [2,3] cat PrimeDivisors(N));
    kerpol0op := Polynomial([m0op(c) : c in Coefficients(kerpol0)]);
    kerpol := kerpol0op;
  else
    kerpol := kerpol;
  end if;

  return kerpol;
end function;


//===============================================================
//
//
// Revised torsion kerpol algorithm
//
//
//===============================================================

RevTorsionKerpol := function(sigma, delta_type, prec);
  // This function computes the kernel polynomial by finding its
  // roots algebraically as x-coordinates of torsion points on EDelta
  // Setup and step 1 in Algorithm 3.2.2

  N := GetN(sigma, delta_type);
  if N eq 1 then
    return 1;
  end if;

  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    E := EllipticCurve([0,1]);
    K := NumberField(Polynomial([1,1,1]));
  else
    E := EllipticCurve([-1,0]);
    K := NumberField(Polynomial([1,0,1]));
  end if;
  phiN := DivisionPolynomial(E, N);


  // Step 2 in Algorithm 3.2.2


  RQ := PolynomialRing(RationalField());
  remainingPoly:= phiN;
  divisors := Divisors(N);
  Exclude(~divisors, N);
  properDivisorDivpols := [DivisionPolynomial(E,m): m in divisors ];
  for pol in properDivisorDivpols do
    gcd := GreatestCommonDivisor(RQ!pol, RQ!remainingPoly);
    remainingPoly := RQ!(remainingPoly/gcd);
  end for;


  // Step 3 in Algorithm 3.2.2


  RK:=PolynomialRing(K);
  remainingPoly := RK!remainingPoly;
  factors := [pair[1] : pair in Factorization(remainingPoly)];
  orderedFactors := Sort(factors);

  // Choose a factor with rational coefficients if possible (to simplify field extensions)

  highestDegree := Degree(orderedFactors[#orderedFactors]);
  simplerCandidates := [ ];
  for factor in orderedFactors do
    if (Degree(factor) eq highestDegree) and (Coefficients(factor) subset Rationals()) then
      Append(~simplerCandidates, factor);
    end if;
  end for;

  if #simplerCandidates ge 1 then
    gN := simplerCandidates[#simplerCandidates];
  else
    gN := orderedFactors[#orderedFactors];
  end if;

  L := ext<K|gN>;
  RL<x> := PolynomialRing(L);

  // Finding the x-coordinate for a generator of E[N] as a Z[j] module

  gN := RL!gN;
  if L eq K then
    bool, Px := HasRoot(gN);
  else
    Px := L.1;
  end if;

  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    j := L!K.1;
    k := 1;
    jPx := j*Px; 
  else
    j := L!K.1;
    k := j; 
    jPx := -Px;
  end if;


  //Taking points that will give distinct x-coordinates

  lattice := [ [a,b] : a in [0..N], b in [0..N]];
  lattice := Sort(lattice);
  cutoff := Ceiling(#lattice/2);
  coors := [lattice[n]: n in [1..cutoff]];
  firstRowFirstHalf := [[0,x] : x in [0..Floor((N-1)/2)] ];
  lastColumn := [[x, N] : x in [0..N]];
  cuts := firstRowFirstHalf cat lastColumn;
  for cut in cuts do
     Exclude(~coors, cut);
  end for;


  //Construct necessary division polynomials evaluated at Px

  FL<x,y> := FunctionField(L,2);
  D := [* *];
  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    swap := FL!(Px^3 + 1);
    Append(~D, FL!0);
    Append(~D, FL!1);
    Append(~D, FL!(2*y));
    Append(~D, FL!(3*Px^4 + 12*Px));
    Append(~D, FL!(4*y*(Px^6+20*Px^3-8)));
  else
    swap := FL!(Px^3 -Px);
    Append(~D, FL!0);
    Append(~D, FL!1);
    Append(~D, FL!(2*y));
    Append(~D, FL!(3*Px^4 -6*Px^2-1));
    Append(~D, FL!(4*y*(Px^6-5*Px^4-5*Px^2+1)));
  end if;

  if N ge 3 then
    for n in [5..N+2] do
      if IsOdd(n) then
	m := ((n-1)/2);
	m := Integers()!m;
	Append(~D, D[m+3]*D[m+1]^3-D[m]*D[m+2]^3);     
      else
	m:= n/2;
	m := Integers()!m;
	Append(~D, (D[m+1]/(2*y))*(D[m+3]*D[m]^2-D[m-1]*D[m+2]^2));
      end if;
    end for;
  end if;


  //Construct the nth X-coordinate maps
  preXmaps := [* *];
  for n in [1..N-1] do
    Append(~preXmaps, Px - D[n]*D[n+2]/D[n+1]^2);
  end for;
  Xmaps := [* *];
  for map in preXmaps do
    Append(~Xmaps, subysquar(map, swap));
  end for;

  //Next construct the nth B maps
  preBmaps := [* *];
  for n in [2..N-1] do
    Append(~preBmaps, (D[n+3]*D[n]^2-D[n-1]*D[n+2]^2)/D[n+1]^3);
  end for;
  Bmaps := [* *];
  for map in preBmaps do
    Append(~Bmaps, subysquar(map, swap));
  end for;


  Xs := [Evaluate(f, [Px,1]): f in Xmaps];
  Bs := [Evaluate(f, [Px,1]): f in Bmaps];
  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    Xjs := [j*p: p in Xs];
    Bjs := Bs;
  else
    Xjs := [-p : p in Xs];
    Bjs := [-p : p in Bs];
  end if;


  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    ysq := Px^3 + 1; 
    Y_nSqs := [Xs[n]^3 + 1 : n in [1..N-1]]; 
  else
    ysq := (Px^3-Px);
    Y_nSqs := [Xs[n]^3 - Xs[n]: n in [1..N-1]];
  end if;

  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then 
    Y_njSqs := [Xjs[n]^3 +1 : n in [1..N-1]];   
  else
    Y_njSqs := [Xjs[n]^3 - Xjs[n] : n in [1..N-1]];     
  end if;

  orbit := [];

  //Step 4 in algorithm 3.2.2

  for pair in coors do
    a := pair[1];
    b := pair[2];
    if a eq 0 then
      out := Xjs[b];
    elif b eq 0 then
      out := Xs[a];
    else
      X_a := Xs[a];
      X_bj := Xjs[b];

      if a ge 2 then
	B_a := Bs[a-1];
      else
	B_a := 4*ysq;
      end if;

      if b ge 2 then
	B_bj := Bjs[b-1];
      else
	B_bj := 4*k^2*ysq;
      end if;

      Y_aSq := Y_nSqs[a];
      Y_bjSq := Y_njSqs[b];
  
      if ysq eq 0 then
	Y_aY_bj := 0;
      else
	Y_aY_bj := (1/(16*k*ysq))*B_a*B_bj;
      end if;

      lamSq := (Y_bjSq - 2*Y_aY_bj + Y_aSq)/(X_bj-X_a)^2;
      out := lamSq - X_a - X_bj;
    end if;
    Append(~orbit, out);
  end for;

  algRootCandidates := orbit cat [0];

  // Step 4 in Algorithm 3.2.5

  compRoots := FindComplexRoots(sigma, delta_type, prec);

  // Step 5 in Algorithm 3.2.5

  v := InfinitePlaces(L)[1];

  rootsInCC := [Evaluate(L!r, v : Precision := prec) : r in algRootCandidates];
  algRoots := [ ];
  if (#compRoots ge 1 and #rootsInCC ge 1) then
    for root in compRoots do
      rootsDif := [AbsoluteValue(root - CCroot) : CCroot in rootsInCC];
      minDiff, index := Minimum(rootsDif);
      match := algRootCandidates[index];
      Append(~algRoots, match);
    end for;
  end if;

  // Step 6 in Algorithm 3.2.5

  RK<xK> := PolynomialRing(L);
  if #algRoots ge 1 then
    kerpol := &*[xK - root : root in algRoots];
  else
    kerpol := 1;
  end if;

  // Simplifying kerpol if possible

  if Type(kerpol) ne RngIntElt then
    if L eq Rationals() then
      K0 := L;
    else
      K0:= sub<L|Coefficients(kerpol)>;
    end if;
    kerpol0 := Polynomial(ChangeUniverse(Eltseq(kerpol), K0));
    if K0 eq Rationals() then
      K0op, m0op := OptimizedRepresentation(K0 : Ramification := [2,3] cat PrimeDivisors(N));
    else
      f0, K01seq := Polredabs(MinimalPolynomial(K0.1));
      K0op := NumberField(f0);
      m0op := hom<K0 -> K0op | K0op!K01seq>;
    end if;
    // K0op, m0op:=OptimizedRepresentation(K0 : Ramification := [2,3] cat PrimeDivisors(N));
    kerpol0op := Polynomial([m0op(c) : c in Coefficients(kerpol0)]);
    kerpol := kerpol0op;
  else
    kerpol := kerpol;
  end if;
  return kerpol;
end function;

//===============================================================
//
//
// Hybrid kerpol algorithm
//
//
//================================================================

HybridKerpol := function(sigma, delta_type, prec);
  // This function computes the kernel polynomial by first selecting the factors of 
  // the Nth division polynomial over E that contain the roots of our kernel polynomial
  // then constructing a field where those factors split and finding the roots as algebraic numbers
  facs := ChooseDivisionPolyFactors(sigma, delta_type, prec);
  N := GetN(sigma, delta_type);
  if N eq 1 then
    algRootCandidates := [];
  else
		if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
			E := EllipticCurve([0,1]);
			K := NumberField(Polynomial([1,-1,1]));
			alp := K.1;
		else
			E := EllipticCurve([-1,0]);
			K := NumberField(Polynomial([1,0,1]));
		end if;

		// Building the field L from Algorithm 3.2.2

		phiN := DivisionPolynomial(E, N);
		RQ := PolynomialRing(RationalField());
		remainingPoly:= phiN;
		divisors := Divisors(N);
		Exclude(~divisors, N);
		properDivisorDivpols := [DivisionPolynomial(E,m): m in divisors ];
		for pol in properDivisorDivpols do
			gcd := GreatestCommonDivisor(RQ!pol, RQ!remainingPoly);
			remainingPoly := RQ!(remainingPoly/gcd);
		end for;
		RK:=PolynomialRing(K);
		remainingPoly := RK!remainingPoly;
		factors := [pair[1] : pair in Factorization(remainingPoly)];
		orderedFactors := Sort(factors);

		highestDegree := Degree(orderedFactors[#orderedFactors]);
		simplerCandidates := [ ];
		for factor in orderedFactors do
			if (Degree(factor) eq highestDegree) and (Coefficients(factor) subset Rationals()) then
				Append(~simplerCandidates, factor);
			end if;
		end for;

		if #simplerCandidates ge 1 then
			gN := simplerCandidates[1];
		else
			gN := orderedFactors[#orderedFactors];
		end if;
		L1 := ext<K|gN>;

		// Taking roots of the division polynomial factors

		RL1<X>:=PolynomialRing(L1);
		facsInRL1 := [RL1!fac: fac in facs];
		rootMults := [Roots(fac): fac in facsInRL1];
		allRootMults := [x : x in y, y in rootMults];
		algRootCandidates := [pair[1]: pair in allRootMults];
  end if;

  // Matching roots with our complex roots

  compRoots := FindComplexRoots(sigma, delta_type, prec);
  if #algRootCandidates ge 1 then
    L2 :=Parent(algRootCandidates[1]); 
    v := InfinitePlaces(L2)[1];
    rootsInCC := [Evaluate(r, v : Precision := prec) : r in algRootCandidates];
  else
    rootsInCC := [ ];
    L2 := Rationals();
  end if;

  algRoots := [ ];
  if (#compRoots ge 1 and #rootsInCC ge 1) then
    for root in compRoots do
      rootsDif := [AbsoluteValue(root - CCroot) : CCroot in rootsInCC];
      minDiff, index := Minimum(rootsDif);
      match := algRootCandidates[index];
      Append(~algRoots, match);
    end for;
  end if;

  // Building kernel polynomial and simplifying if possible

  RK<xK> := PolynomialRing(L2);
  if #algRoots ge 1 then
    kerpol := &*[xK - root : root in algRoots];
  else
    kerpol := 1;
  end if;
  if Type(kerpol) ne RngIntElt then
    if L2 eq Rationals() then
      K0 := L2;
    else
      K0:= sub<L2|Coefficients(kerpol)>;
    end if;
    kerpol0 := Polynomial(ChangeUniverse(Eltseq(kerpol), K0));
    if K0 eq Rationals() then
      K0op, m0op:=OptimizedRepresentation(K0 : Ramification := [2,3] cat PrimeDivisors(N));
    else
      f0, K01seq := Polredabs(MinimalPolynomial(K0.1));
      K0op := NumberField(f0);
      m0op := hom<K0 -> K0op | K0op!K01seq>;
    end if;
    kerpol0op := Polynomial([m0op(c) : c in Coefficients(kerpol0)]);
    kerpol := kerpol0op;
  else
    kerpol := kerpol;
  end if;
  return kerpol;
end function;

//===============================================================
//
//
// Splitting kerpol algorithm
//
//
//================================================================

SplittingKerpol := function(sigma, delta_type, prec);
  // This function computes our kernel polynomial by selecting the factors of the Nth divvision
  // polynomial over E that contain the roots we need then splitting those factors in a common field
  // constructed with extensions and iteratively taking compositums
  pols := ChooseDivisionPolyFactors(sigma, delta_type, prec);
  comproots:= FindComplexRoots(sigma, delta_type, prec);
  N:= GetN(sigma, delta_type);
  spliFis := [* *];
  rootLists := [* *];
  K := Rationals();

  // Iteratively extend QQ until it contains all the roots we need and collect roots

  for g in pols do
    Kg, Rg := SplittingField(g);
    Append(~spliFis, Kg);
    Append(~rootLists, Rg);
    K := Compositum(K, Kg);
  end for;
  rootsInK := [ ];
  for i in [1..#rootLists] do
    for j in [1..#rootLists[i]] do 
      Append(~rootsInK, K!rootLists[i][j]);
    end for;
  end for;

  // Match algebraic roots found above to our complex roots

  v := InfinitePlaces(K)[1];
  rootsInCC := [Evaluate(r, v : Precision := prec) : r in rootsInK];
  algRoots := [ ];
  if (#comproots ge 1 and #rootsInCC ge 1) then
    for root in comproots do
      rootsDif := [AbsoluteValue(root - CCroot) : CCroot in rootsInCC];
      minDiff, index := Minimum(rootsDif);
      match := rootsInK[index];
      Append(~algRoots, match);
    end for;
  end if;

  // Build kernel polynomial and simplify if possible

  RK<xK> := PolynomialRing(K);
  if #algRoots ge 1 then
    kerpol := &*[xK - root : root in algRoots];
  else
    kerpol := 1;
  end if;
  if Type(kerpol) ne RngIntElt then
    if K eq Rationals() then
      K0 := K;
    else
      K0:= sub<K|Coefficients(kerpol)>;
    end if;

    kerpol0 := Polynomial(ChangeUniverse(Eltseq(kerpol), K0));

    if K0 eq Rationals() then
      K0op, m0op:=OptimizedRepresentation(K0 : Ramification := [2,3] cat PrimeDivisors(N));
    else
      f0, K01seq := Polredabs(MinimalPolynomial(K0.1));
      K0op := NumberField(f0);
      m0op := hom<K0 -> K0op | K0op!K01seq>;
    end if;
    kerpol0op := Polynomial([m0op(c) : c in Coefficients(kerpol0)]);
    return kerpol0op;
  else
    return kerpol;
  end if;
end function;

//===============================================================
//
//
// Cyclic Reduction Kerpol algorithm
//
//
//===============================================================
CycRedKerpol := function(sigma, delta_type, prec);
  N := Integers()!GetN(sigma, delta_type);
  g := Getg(sigma, delta_type);
  b := GetBasis(sigma, delta_type);
  n1 := Integers()!b[1][1]/g;
  n2 := Integers()!b[1][2];
  m2 := Integers()!b[2][2]/g;

  if N eq 1 then
    return 1;
  end if;

  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    E := EllipticCurve([0,1]);
    K := NumberField(Polynomial([1,1,1]));
  else
    E := EllipticCurve([-1,0]);
    K := NumberField(Polynomial([1,0,1]));
  end if;

  if g ge 2 then
	N := Integers()!(N/(g^2));
  end if;
  phiN := DivisionPolynomial(E, N);

  if N eq 1 then
    return DivisionPolynomial(E,g);
  end if;


  // Step 2 in Algorithm 3.2.2


  RQ := PolynomialRing(RationalField());
  remainingPoly:= phiN;
  divisors := Divisors(N);
  Exclude(~divisors, N);
  properDivisorDivpols := [DivisionPolynomial(E,m): m in divisors ];
  for pol in properDivisorDivpols do
    gcd := GreatestCommonDivisor(RQ!pol, RQ!remainingPoly);
    remainingPoly := RQ!(remainingPoly/gcd);
  end for;


  // Step 3 in Algorithm 3.2.2


  RK:=PolynomialRing(K);
  remainingPoly := RK!remainingPoly;
  factors := [pair[1] : pair in Factorization(remainingPoly)];
  orderedFactors := Sort(factors);

  // Finding the x-coordinate for a cyclic generator of the kernel 

  highestDegree := Degree(orderedFactors[#orderedFactors]);
  simplerCandidates := [ ];
  for factor in orderedFactors do
    if (Degree(factor) eq highestDegree) and (Coefficients(factor) subset Rationals()) then
      Append(~simplerCandidates, factor);
    end if;
  end for;

  if #simplerCandidates ge 1 then
    gN := simplerCandidates[#simplerCandidates];
  else
    gN := orderedFactors[#orderedFactors];
  end if;

  L := ext<K|gN>;
  RL<xL> := PolynomialRing(L);
  gN := RL!gN;
  if L eq K then
    bool, Px := HasRoot(gN);
  else
    Px := L.1;
  end if;

  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    j := L!K.1;
    k := 1;
    jPx := j*Px; 
  else
    j := L!K.1;
    k := j; 
    jPx := -Px;
  end if;

  v := InfinitePlaces(L)[1];

  poss := [[t1*n1, t1*n2 + t2*m2] : t1 in [0..m2-1], t2 in [0..n1-1]];
  foundGen := false;
  i := 1;
  while foundGen eq false do
    check := poss[i];
    orb := [[(Integers()!(l*check[1])) mod Integers()!N, (Integers()!(l*check[2])) mod Integers()!N] : l in [1..N]];
    if #Set(orb) eq N then
      gen := check;
      foundGen := true;
    else
      i := i + 1;
    end if;
  end while;

  compGener := EllipticExponential(E,[gen[1]/N, gen[2]/N] : Precision := prec)[1];
  plugFacs := [* *];
  for fac in orderedFactors do
    coeffs := Coefficients(fac);
    newcoeffs := [Evaluate(L!c, v : Precision := prec) : c in coeffs];
    newFac := Polynomial(newcoeffs);
    Append(~plugFacs, newFac);
  end for;

  plugIns := [AbsoluteValue(Evaluate(fac,compGener)) : fac in plugFacs];
  minPlug, index := Minimum(plugIns);
  minp := RL!orderedFactors[index];
  
  cands := [r[1]:r in Roots(minp)];
  candsInCC := [Evaluate(L!cand, v : Precision := prec) : cand in cands];
  candsDif := [AbsoluteValue(compGener - CCcand) : CCcand in candsInCC];
  minCandDiff, index := Minimum(candsDif);

  Px := cands[index];

  FL<x,y> := FunctionField(L,2);
  D := [* *];
  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    swap := FL!(Px^3 + 1);
    Append(~D, FL!0);
    Append(~D, FL!1);
    Append(~D, FL!(2*y));
    Append(~D, FL!(3*Px^4 + 12*Px));
    Append(~D, FL!(4*y*(Px^6+20*Px^3-8)));
  else
    swap := FL!(Px^3 -Px);
    Append(~D, FL!0);
    Append(~D, FL!1);
    Append(~D, FL!(2*y));
    Append(~D, FL!(3*Px^4 -6*Px^2-1));
    Append(~D, FL!(4*y*(Px^6-5*Px^4-5*Px^2+1)));
  end if;

  rep := Floor(N/2)+2;
  if rep ge 5 then
    for n in [5..rep] do
      if IsOdd(n) then
	  m := ((n-1)/2);
	  m := Integers()!m;
	  Append(~D, D[m+3]*D[m+1]^3-D[m]*D[m+2]^3);
      else
	  m:= n/2;
	  m := Integers()!m;
	  Append(~D, (D[m+1]/(2*y))*(D[m+3]*D[m]^2-D[m-1]*D[m+2]^2));
      end if;
    end for;
  end if;

  //Construct the nth X-coordinate maps
  preXmaps := [* *];
  for n in [1..Floor(N/2)] do
    Append(~preXmaps, Px - D[n]*D[n+2]/D[n+1]^2);
  end for;
  Xmaps := [* *];
  for map in preXmaps do
    Append(~Xmaps, subysquar(map, swap));
  end for;
  Xs := [Evaluate(f, [Px,1]): f in Xmaps];

  // Step 6 in Algorithm 3.2.5

  if #Xs ge 1 then
    kerpol := &*[xL - root : root in Xs];
  else
    kerpol := 1;
  end if;


  if g ge 2 then
    phig := RL!DivisionPolynomial(E,g);
    kerpol := RL!((phig*kerpol)/xL);
  end if;


  // Simplifying kerpol if possible

  if Type(kerpol) ne RngIntElt then
    if L eq Rationals() then
      K0 := L;
    else
      K0:= sub<L|Coefficients(kerpol)>;
    end if;
    kerpol0 := Polynomial(ChangeUniverse(Eltseq(kerpol), K0));
    if K0 eq Rationals() then
      K0op, m0op := OptimizedRepresentation(K0 : Ramification := [2,3] cat PrimeDivisors(N));
    else
      f0, K01seq := PolredabsWithRoot(MinimalPolynomial(K0.1));
      K0op := NumberField(f0);
      m0op := hom<K0 -> K0op | K0op!K01seq>;
    end if;
    // K0op, m0op:=OptimizedRepresentation(K0 : Ramification := [2,3] cat PrimeDivisors(N));
    kerpol0op := Polynomial([m0op(c) : c in Coefficients(kerpol0)]);
    kerpol := kerpol0op;
  else
    kerpol := kerpol;
  end if;
  return kerpol;
end function;



//===============================================================
//
//
// Splitting with proper cyclic factor
//
//
//================================================================

SmallerSplittingKerpol := function(sigma, delta_type, prec);
  N := Integers()!GetN(sigma, delta_type);
  g := Getg(sigma, delta_type);
  b := GetBasis(sigma, delta_type);
  n1 := Integers()!b[1][1]/g;
  n2 := Integers()!b[1][2];
  m2 := Integers()!b[2][2]/g;

  if N eq 1 then
    return 1;
  end if;

  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    E := EllipticCurve([0,1]);
    K := NumberField(Polynomial([1,1,1]));
  else
    E := EllipticCurve([-1,0]);
    K := NumberField(Polynomial([1,0,1]));
  end if;

  if g ge 2 then
	N := Integers()!(N/(g^2));
  end if;
  phiN := DivisionPolynomial(E, N);

  if N eq 1 then
    return DivisionPolynomial(E,g);
  end if;


  // Step 2 in Algorithm 3.2.2


  RQ := PolynomialRing(RationalField());
  remainingPoly:= phiN;
  divisors := Divisors(N);
  Exclude(~divisors, N);
  properDivisorDivpols := [DivisionPolynomial(E,m): m in divisors ];
  for pol in properDivisorDivpols do
    gcd := GreatestCommonDivisor(RQ!pol, RQ!remainingPoly);
    remainingPoly := RQ!(remainingPoly/gcd);
  end for;


  // Step 3 in Algorithm 3.2.2


  RK:=PolynomialRing(K);
  remainingPoly := RK!remainingPoly;
  factors := [pair[1] : pair in Factorization(remainingPoly)];
  orderedFactors := Sort(factors);

  highestDegree := Degree(orderedFactors[#orderedFactors]);
  simplerCandidates := [ ];
  for factor in orderedFactors do
    if (Degree(factor) eq highestDegree) and (Coefficients(factor) subset Rationals()) then
      Append(~simplerCandidates, factor);
    end if;
  end for;

  if #simplerCandidates ge 1 then
    gN := simplerCandidates[#simplerCandidates];
  else
    gN := orderedFactors[#orderedFactors];
  end if;


  L := ext<K|gN>;
  RL<xL> := PolynomialRing(L);
  phiN := RL!phiN;
  comproots:= WFindComplexRoots(sigma, delta_type, prec, g);
  v := InfinitePlaces(L)[1];
  cands := [r[1]:r in Roots(phiN)] cat [0];
  rootsInCC := [Evaluate(r, v : Precision := prec) : r in cands];
  algRoots := [ ];
  if (#comproots ge 1 and #rootsInCC ge 1) then
    for root in comproots do
      rootsDif := [AbsoluteValue(root - CCroot) : CCroot in rootsInCC];
      minDiff, index := Minimum(rootsDif);
      match := cands[index];
      Append(~algRoots, match);
    end for;
  end if;

  // Step 6 in Algorithm 3.2.5

  if #algRoots ge 1 then
    kerpol := &*[xL - root : root in algRoots];
  else
    kerpol := 1;
  end if;


  if g ge 2 then
    phig := RL!DivisionPolynomial(E,g);
    kerpol := RL!((phig*kerpol)/xL);
  end if;

  // Simplifying kerpol if possible

  if Type(kerpol) ne RngIntElt then
    if L eq Rationals() then
      K0 := L;
    else
      K0:= sub<L|Coefficients(kerpol)>;
    end if;
    kerpol0 := Polynomial(ChangeUniverse(Eltseq(kerpol), K0));
    if K0 eq Rationals() then
      K0op, m0op := OptimizedRepresentation(K0 : Ramification := [2,3] cat PrimeDivisors(N));
    else
      f0, K01seq := PolredabsWithRoot(MinimalPolynomial(K0.1));
      K0op := NumberField(f0);
      m0op := hom<K0 -> K0op | K0op!K01seq>;
    end if;
    // K0op, m0op:=OptimizedRepresentation(K0 : Ramification := [2,3] cat PrimeDivisors(N));
    kerpol0op := Polynomial([m0op(c) : c in Coefficients(kerpol0)]);
    kerpol := kerpol0op;
  else
    kerpol := kerpol;
  end if;
  return kerpol;
end function;

//===============================================================
//
//
// Functions for steps 7 and 8 in Algorithm 3.2.5
// (Once the kernel polynomial has been found)
//
//
//================================================================

FindIsogenyXTDtoXTGFromKerPol := function(presigma, delta_type, prec, kerpol)
  // Given a kernel polynomial, this function calculates the corresponding
  // isogeny from E(Delta) to E(Gamma)
  sigma, vertnumber, r := PreProcessingConjugation(presigma, delta_type);
  if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
    E := EllipticCurve([0,1]);
  else
    E := EllipticCurve([-1,0]);
  end if;
  if Type(kerpol) ne RngIntElt then
    curve, map := IsogenyFromKernel(BaseExtend(E, BaseRing(kerpol)), kerpol);
  else
    curve := E;
    map := 1;
  end if;
  return curve, map;
end function;

FindIsogenyXTGtoXTD := function(presigma, delta_type, prec, kerpol);
  // This function determines the isogeny from E(Gamma) to E(Delta)
  a,b := FindIsogenyXTDtoXTGFromKerPol(presigma, delta_type, prec, kerpol);
  if Type(b) ne RngIntElt then
    map := DualIsogeny(b);
  else
    map := 1;
  end if;
  return map, a;
end function;

FindNiceIsogenyXTGtoXTD := function(presigma, delta_type, prec, kerpol);
  // This function returns the isogeny from E(Gamma) to E(Delta) in a simplified format
  psi, XTGeq := FindIsogenyXTGtoXTD(presigma, delta_type, prec, kerpol);
  if Type(psi) eq RngIntElt then
    psinice := 1;
  else
    if BaseField(Domain(psi)) ne RationalField() then
      KO<alpha> := BaseField(Domain(psi));
    end if;
    defeqs := DefiningEquations(psi);
    R<x,y,z> := Universe(defeqs);
    psix := defeqs[1]/defeqs[3];
    psiy := defeqs[2]/defeqs[3];

    FracR<x,y,z> := Parent(psix);
    psixnice := Evaluate(psix,[x,y,1]);
    psiynice := Evaluate(psiy,[x,y,1]);
    psinice := [psixnice, psiynice];
  end if;
  return psinice, XTGeq;
end function;

//===============================================================
//
//
// Functions for steps 5 and 6 in Algorithm 3.5.1
// (tracing around the master diagram to find phi)
//
//
//================================================================

substituteforxcube_poly := function(phi, xcubesub);
  // this function takes as input phi, a polynomial in x and y,
  // which is in fact a rational function in x^3 and y,
  // and returns as output what you get by substituting xcubesub in for x^3
  mons := Monomials(phi);
  cfs := Coefficients(phi);
  phisub := Parent(phi)!0;
  _<x,y> := Parent(phi);
  for i := 1 to #mons do
    e := Exponents(mons[i]);
    assert e[1] mod 3 eq 0;
    phisub +:= cfs[i]*xcubesub^(e[1] div 3)*y^e[2];
  end for;
  
  return phisub;
end function;

substituteforxcube := function(phi, xcubesub);
  // this function takes as input phi, a *rational function* in x and y,
  // and plugs it into the poly version by numerator and denominator
  return substituteforxcube_poly(Numerator(phi), xcubesub)/substituteforxcube_poly(Denominator(phi), xcubesub);
end function;

substituteforxsquar_poly := function(phi, xsquarsub);
  // this function takes as input phi, a polynomial in x and y,
  // which is in fact a rational function in x^2 and y,
  // and returns as output what you get by substituting xsquarsub in for x^2
  mons := Monomials(phi);
  cfs := Coefficients(phi);
  phisub := Parent(phi)!0;
  _<x,y> := Parent(phi);
  for i := 1 to #mons do
    e := Exponents(mons[i]);
    assert e[1] mod 2 eq 0;
    phisub +:= cfs[i]*xsquarsub^(e[1] div 2)*y^e[2];
  end for;  
  return phisub;
end function;

substituteforxsquar := function(phi, xsquarsub);
  // this function takes as input phi, a *rational function* in x and y,
  // and plugs it into the poly version by numerator and denominator
  return substituteforxsquar_poly(Numerator(phi), xsquarsub)/substituteforxsquar_poly(Denominator(phi), xsquarsub);
end function;

substituteforysquar_poly := function(phi, ysquarsub);
  // this function takes as input phi, a polynomial in x and y,
  // which is in fact a rational function in x and y^2,
  // and returns as output what you get by substituting ysquarsub in for y^2
  mons := Monomials(phi);
  cfs := Coefficients(phi);
  phisub := Parent(phi)!0;
  _<x,y> := Parent(phi);
  ysquarsub := Evaluate(ysquarsub,[x,y,1]);
  for i := 1 to #mons do
    e := Exponents(mons[i]);
    assert e[2] mod 2 eq 0;
    phisub +:= cfs[i]*ysquarsub^(e[2] div 2)*x^e[1];
  end for;  
  return phisub;
end function;

substituteforysquar := function(phi, ysquarsub);
  // this function takes as input phi, a *rational function* in x and y,
  // and plugs it into the poly version by numerator and denominator
  num := substituteforysquar_poly(Numerator(phi), ysquarsub);
  den := substituteforysquar_poly(Denominator(phi), ysquarsub);
  return num/den;
end function;

substitutefory_poly := function(phi, ysub);
  // this function takes as input phi, a polynomial in x and y,
  // which is in fact a rational function in x and y,
  // and returns as output what you get by substituting ysub in for y
  mons := Monomials(phi);
  cfs := Coefficients(phi);
  phisub := Parent(phi)!0;
  _<x,y> := Parent(phi);
  for i := 1 to #mons do
    e := Exponents(mons[i]);
    assert e[2] mod 1 eq 0;
    phisub +:= cfs[i]*ysub^(e[2])*x^e[1];
  end for; 
 
  return phisub;
end function;

substitutefory := function(phi, ysub);
  // this function takes as input phi, a *rational function* in x and y,
  // and plugs it into the poly version by numerator and denominator
  return substitutefory_poly(Numerator(phi), ysub)/substitutefory_poly(Denominator(phi), ysub);
end function;

substituteforyfour_poly := function(phi, yfoursub);
  // this function takes as input phi, a polynomial in x and y,
  // which is in fact a rational function in x and y^4,
  // and returns as output what you get by substituting yfoursub in for y^4
  mons := Monomials(phi);
  cfs := Coefficients(phi);
  phisub := Parent(phi)!0;
  _<x,y> := Parent(phi);
  for i := 1 to #mons do
    e := Exponents(mons[i]);
    assert e[2] mod 4 eq 0;
    phisub +:= cfs[i]*x^(e[1])*yfoursub^(e[2] div 4);
  end for;  
  return phisub;
end function;

substituteforyfour := function(phi, yfoursub);
  // this function takes as input phi, a *rational function* in x and y,
  // and plugs it into the poly version by numerator and denominator
  return substituteforyfour_poly(Numerator(phi), yfoursub)/substituteforyfour_poly(Denominator(phi), yfoursub);
end function;


ComputeEucBelyiMap := function(presigma, delta_type, prec : Al := "Cyc");
  // This function takes a transitive Euclidean permutation triple and constructs the corresponding Belyi map
  // and optionally allows users to choose which method is used to compute the kernel polynomial of the relevant isogeny
  sigma, vertnumber, size := PreProcessingConjugation(presigma, delta_type);
  R := GetR(sigma, delta_type);

  if Al eq "Torsion" then
    kerpol := TorsionKerpol(sigma, delta_type, prec);
  elif Al eq "Hybrid" then
    kerpol := HybridKerpol(sigma, delta_type, prec);
  elif Al eq "Splitting" then 
    kerpol := SplittingKerpol(sigma, delta_type, prec);
  elif Al eq "Rev" then
    kerpol := RevTorsionKerpol(sigma, delta_type, prec);
  elif Al eq "Cyc" then
    kerpol := CycRedKerpol(sigma, delta_type, prec);
  end if;

  phi, XTG:= FindNiceIsogenyXTGtoXTD(sigma, delta_type, prec, kerpol);

  if Type(phi) ne RngIntElt then
    X := phi[1];
    Y := phi[2];
  else
    Rprov<X,Y>:=PolynomialRing(Rationals(),2);
  end if;
  if delta_type eq [3,3,3] then
    comp := (Y + 1)/2;
  elif delta_type eq [2,4,4] then
    if vertnumber eq 1 then
      comp := (X + 1)^2/(X-1)^2;
    elif vertnumber eq 2 then
      comp := X^2;
    else
      comp := X^2;
    end if;
  else
    if vertnumber eq 1 then       
      if (Type(Parent(X)) ne RngMPol) then
        if BaseField(Parent(X)) ne Rationals() then
          rtsom := Roots(Polynomial([1,-1,1]), BaseField(Parent(X)));
          if #rtsom ge 1 then
            K := BaseField(Parent(X));
            alp := rtsom[1][1];
          else
            K := ext<BaseField(Parent(X)) | Polynomial([1,-1,1])>;
            alp := K.1;
          end if;
        else
          K := ext<Rationals()|Polynomial([1,-1,1])>;
          alp := K.1;
        end if;  
      elif BaseRing(Parent(X)) ne Rationals() then
        K := BaseRing(Parent(X));
        //print "AYo?";
        alp := K!alp;
      else
        K:= ext<Rationals()|Polynomial([1,-1,1])>;
        alp := K.1;
      end if;
      RK<a,b> := RationalFunctionField(K,2);

      if Type(phi) ne RngIntElt then
        XK := Evaluate(X,[a,b,1]);
        YK := Evaluate(Y,[a,b,1]);
      else
        XK := Evaluate(X,[a,b]);
        YK := Evaluate(Y,[a,b]);
      end if;
      comp := ((9*alp - 9)*XK^2 + 9*alp*XK + 9)/(XK^3 + (3*alp - 3)*XK^2 - 3*alp*XK + 1);
    elif vertnumber eq 2 then
      comp := (X^6 + 8*X^3*Y + 8*X^3 + 16*Y^2 + 32*Y + 16)/X^6;
    else
      comp := Y^2;
    end if;          
  end if;

   _<x,y,z> := Parent(Equation(XTG));
  XTGeq := Equation(XTG);
  r := size;
  if r eq 6 then
    swap:=-Evaluate(XTGeq,[0,y,-1]);
    // XTGeq solved for x^3 in terms of y^2
    preout := substituteforxcube(comp, swap);
    out := substituteforysquar(preout, x);
  elif r eq 4 then
    swap := (-Evaluate(XTGeq,[x,0,1]))^2;
    // XTGeq solved for y^4 in terms of x^2
    preout := substituteforyfour(comp, swap);
    out := substituteforxsquar(preout, x);
  elif r eq 3 then
    swap := -Evaluate(XTGeq,[0,y,-1]);
    //print XTG;
    //print swap;
    // XTGeq solved for x^3 in terms of y
    preout := substituteforxcube(comp, swap);
    //print preout;
    out := substitutefory(preout, x);
    //print out;
  elif r eq 2 then
    swap := -Evaluate(XTGeq,[x,0,1]);
    // XTQeq solved for y^2 in terms of x
    preout := substituteforysquar(comp, swap);
    out := preout;
  else
    out := comp;
  end if;

  base := BaseRing(Parent(out));
  if base ne Rationals() then
    coeffs := Coefficients(Numerator(out)) cat Coefficients(Denominator(out)) cat Coefficients(XTG);
    absbase := AbsoluteField(base);
    minField := OptimizedRepresentation(sub<absbase|ChangeUniverse(coeffs,absbase)>);
    coeffsXTG := ChangeUniverse(Coefficients(XTG), minField);
  else
    minField := Rationals();
    coeffsXTG := Coefficients(XTG);
  end if;

  if r eq 1 then
    // means we keep the elliptic curve
    if delta_type eq [3,3,3] or delta_type eq [2,3,6] then
      X := EllipticCurve(coeffsXTG);
    else
      X := EllipticCurve(coeffsXTG);
    end if;
    KX<x,y> := FunctionField(X);
    if Rank(Parent(out)) eq 3 then
      out := Evaluate(out,[x,y,1]);
    else
      out := Evaluate(out,[x,y]);
    end if;
  else
    X := Curve(ProjectiveSpace(PolynomialRing(minField, 2)));
    KX<x> := FunctionField(X);
    if Rank(Parent(out)) eq 3 then
      out := Evaluate(out,[x,x,1]);  // should only be a polynomial in one of these
    else
      out := Evaluate(out,[x,1]);
    end if;
  end if;

  return X, out;
end function;

ComputeFacts := function(sigma, delta_type, prec : Al := "Torsion");
  // This function computes the Euclidean Belyi map corresponding to sigma then returns
  // factorizations of the numerator, denominator, and difference of the rational Belyi map
  curve, phi := ComputeEucBelyiMap(sigma, delta_type, prec : Al := Al);
  num:= Numerator(phi);
  den:= Denominator(phi);
  dif := num-den;
  numfac:= Factorization(num);
  denfac:= Factorization(den);
  diffac:= Factorization(dif);
  return [numfac, denfac, diffac];
end function;




