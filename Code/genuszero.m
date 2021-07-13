// ================================================================================
// Genus zero
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

intrinsic TrianglePhiGenusZeroRecognizeSeries(Skb::SeqEnum[RngSerPowElt], Gamma::GrpPSL2Tri) -> Any
{Takes as input recognized power series over the ground field and returns the Belyi map as a rational function.}
  Theta := Gamma`TriangleTheta;

  Delta := ContainingTriangleGroup(Gamma);
  phi, kappa := TrianglePhi(Delta);
  CC := Parent(kappa);
  a := DefiningABC(Gamma)[1];

  alpha := 1/(Gamma`TriangleTheta*kappa)^a;

  K,v := TriangleK(Gamma);
  ZK := Integers(K);
  ZKbCC := [Evaluate(b,v : Precision := Precision(CC)) : b in Basis(ZK)];

  m := Degree(K);
  if m eq 1 then
    lin := LinearRelation(ZKbCC cat [-alpha] cat [CC.1] : Al := "LLL");
  else
    lin := LinearRelation(ZKbCC cat [-alpha] : Al := "LLL");
  end if;

  alpha := (ZK!lin[1..m])/lin[m+1];

  phies := AbsEltseq(phi);
  phies := ChangeUniverse(phies, K);
  for i := 1 to ((#phies-1) div a) do
    phies[a*i+1] := phies[a*i+1]*alpha^i;
  end for;
  phi := Universe(Skb)!phies;

  h := Skb[#Skb];
  g := Skb[#Skb-1];

  sigma := DefiningPermutation(Gamma);
  a := DefiningABC(Gamma)[1];
  e := a div #CycleDecomposition(sigma[1])[1];
  d := IndexDegree(Gamma);

  chg := Coefficient(h, Degree(LeadingTerm(h))+e);
  xx := Universe(Skb)!(h/(g+chg*h)) + O(Parent(h).1^(3*e*d));
  assert Degree(LeadingTerm(xx)) eq e and Coefficient(xx,2*e) eq 0;

  M := Matrix([[Coefficient(f,e*n) : n in [1..2*d]]  : f in [xx^i : i in [1..d]] cat [ xx^i*phi : i in [0..d]]]);
  kerM := Kernel(M);
  if Dimension(kerM) gt 1 then
    derr := d+Dimension(kerM);
    xx := Universe(Skb)!(h/(g+chg*h)) + O(Parent(h).1^(3*e*derr));
    M := Matrix([[Coefficient(f,e*n) : n in [1..2*derr]]  : f in [xx^i : i in [1..d]] cat [ xx^i*phi : i in [0..d]]]);
    kerM := Kernel(M);
  end if;
  assert Dimension(kerM) eq 1;
  kerMes := Eltseq(kerM.1);
  phixnum := -Polynomial([0] cat kerMes[1..d]);
  phixden := Polynomial(kerMes[d+1..2*d+1]);
  _<xK> := Parent(phixnum);
  d := Lcm([Denominator(c) : c in Eltseq(phixnum) cat Eltseq(phixden)]);
  phixnum *:= d;
  phixden *:= d;
  Kig := PolynomialRing(K);
  phix := (Kig!phixnum)/(Kig!phixden);

  PP1 := Curve(ProjectiveSpace(PolynomialRing(K, 2)));
  KPP1<x> := FunctionField(PP1);
  phix := Evaluate(phix,x);

  Gamma`TriangleBelyiCurve := PP1;
  Gamma`TriangleBelyiMap := phix;
  return PP1, phix;
end intrinsic;

intrinsic TrianglePhiGenusZeroNumericalBelyiMap(Sk::SeqEnum[SeqEnum[RngSerPowElt]], Gamma::GrpPSL2Tri : Al := "ByRamification", m := 0, precNewton := 0, justCC := false) -> Any
  {Al eq "ByRamification", computing the roots via ramification points,
   or "Newton", which computes the roots via ramification and refines to precision precNewton, or
   or "NumericalKernel", which computes the numerical kernel using the power series expansions.
   (If justCC then just return a rational function, do not try to recognize over the algebraic numbers.)}

  CC := BaseRing(Parent(Sk[1][1]));
  prec := Precision(CC);

  // Delete initial terms that are machine zeroes
  eps := 10^(-Precision(CC)/2);

  h, sh := RemoveLeadingZeros(Sk[#Sk][1],eps);
  g, sg := RemoveLeadingZeros(Sk[#Sk-1][1],eps);

  sigma := DefiningPermutation(Gamma);
  a := DefiningABC(Gamma)[1];
  e := a div #CycleDecomposition(sigma[1])[1]; // e is order of stabilizer

  assert sh ge sg;
  ta := Coefficient(h,sg);
  tb := Coefficient(h,sg+e);
  tc := Coefficient(h,sg+2*e);
  td := Coefficient(g,sg);
  te := Coefficient(g,sg+e);
  tf := Coefficient(g,sg+2*e);
  chg := (-ta*td*tf + ta*te^2 - tb*td*te + tc*td^2);
  cgh := (ta^2*tf - ta*tb*te - ta*tc*td + tb^2*td);

  if Al eq "NumericalKernel" then // or "NumericalKernelSetTheta" then
    Delta := ContainingTriangleGroup(Gamma);
    phi, kappa := TrianglePhi(Delta);

    phi := Evaluate(phi, Parent(phi).1/kappa);

    xx := (td*h-ta*g)/(cgh*g+chg*h);
    assert &and[Abs(Coefficient(xx,n)) lt 10^(-Precision(CC)/2) : n in [0..e-1] cat [e+1..2*e-1]];

    d := IndexDegree(Gamma);

    M := Matrix([[Coefficient(f,e*n) : n in [1..2*d+1]]  : f in [xx^i : i in [1..d]] cat [ xx^i*phi : i in [0..d]]]);
    kerM := NumericalKernel(M);
    assert Nrows(kerM) eq 1;

    kerMes := Eltseq(kerM[1]);
    phixnum := -Polynomial([0] cat kerMes[1..d]);
    phixden := Polynomial(kerMes[d+1..2*d+1]);
    _<x> := Parent(phixnum);

    assert Abs(LeadingCoefficient(phixnum)) gt eps;
    assert Abs(LeadingCoefficient(phixden)) gt eps;
    u := LeadingCoefficient(phixnum)/LeadingCoefficient(phixden);
  else  // "ByRamification" or "Newton"
    ram := TriangleRamificationValues(Sk, Gamma : NormalizeByTheta := false);
    fact := TriangleGenusZeroFactorizationPattern(Gamma);

    polsvec := [];
    CC := Parent(ram[1][1][1]);
    _<xCC> := PolynomialRing(CC);

    if Al eq "ByRamification" then
      Theta := TriangleTheta(Sk, Gamma);
    else
      Theta := 1;
    end if;

    for i := 1 to 3 do
      polv := [];
      for j := 1 to #fact[i] do
        rts := [Theta*(td*ram[i][r][#Sk]-ta*ram[i][r][#Sk-1])/(cgh*ram[i][r][#Sk-1]+chg*ram[i][r][#Sk]) : r in fact[i][j][2]];
        print i, j, rts;
        rts_nooo := [r : r in rts | Abs(r) lt 10^(prec/2)]; // nooooooooooooooooooo!
        if #rts_nooo eq #rts then
          Append(~polv, <&*[xCC-r : r in rts], fact[i][j][1]>);
        else
          if #rts_nooo gt 0 then
            Append(~polv, <&*[xCC-r : r in rts_nooo], fact[i][j][1]>);
          else
            Append(~polv, <Parent(xCC)!1, fact[i][j][1]>);
          end if;
          if Al eq "Newton" then
            error "A ramification point apparently has value oo, and this breaks Newton.  Please report and we will treat this case.";
          end if;
        end if;
      end for;
      Append(~polsvec, polv);
    end for;

    aut := #AutomorphismGroup(Gamma);
    if Al eq "ByRamification" and aut gt 1 then
      // renormalize Theta by rescaling factor lambda
      lambdas := [];
      for s := 1 to 3 do
        for fv in polsvec[s] do
          for trycf := 0 to (Degree(fv[1]) div aut)-1 do
            a1 := Coefficient(fv[1],trycf*aut);
            a2 := Coefficient(fv[1],(trycf+1)*aut);
            if Abs(a1) gt eps and Abs(a2) gt eps then
              lambda := (a1/a2)^(1/aut);
              Append(~lambdas, [a1,a2,lambda]);
            end if;
          end for;
        end for;
      end for;
      
      if #lambdas eq 0 then
        error "Unable to normalize by setting two adjacent coefficients equal even with automorphisms, try with a different algorithm";
      end if;
      lambdadat := lambdas[1];
      lambda := lambdadat[3];
      vprintf Shimura : "Taking NEW lambda = %o = %o/%o... \n", ComplexField(6)!lambda, ComplexField(6)!lambdadat[1], ComplexField(6)!lambdadat[2];
      Gamma`TriangleRescalingFactor := lambda;

      polsvecsc := polsvec;
      for i := 1 to 3 do
        for j := 1 to #polsvecsc[i] do
          polsvecsc[i][j][1] := Evaluate(polsvecsc[i][j][1], lambda*xCC)/lambda^Degree(polsvecsc[i][j][1]);
        end for;
      end for;
      polsvec := polsvecsc;
    end if;
  
    phixpol_0 := &*[f[1]^f[2] : f in polsvec[1]];
    phixpol_1 := &*[f[1]^f[2] : f in polsvec[2]];
    phixpol_oo := &*[f[1]^f[2] : f in polsvec[3]];

    degphi_0 := Degree(phixpol_0);
    degphi_1 := Degree(phixpol_1);
    degphi_oo := Degree(phixpol_oo);

    if degphi_0 eq degphi_1 and degphi_1 eq degphi_oo then
      phixoo1 := phixpol_oo-phixpol_1;
      phix01 := phixpol_0-phixpol_1;
      u := Coefficient(phixoo1,0)/Coefficient(phix01,0);   // could take any coefficient here
      vprint Shimura : Max([Abs(c) : c in Coefficients(u*phixpol_0-phixpol_oo-(u-1)*phixpol_1)]);
    else // solve u*phi_0 - phi_oo = v*phi_1
      if degphi_1 eq degphi_oo then
        assert degphi_0 lt degphi_1;
        u := -Coefficient(phixpol_1,degphi_0)+Coefficient(phixpol_oo,degphi_0);
        vprint Shimura : Max([Abs(c) : c in Coefficients(u*phixpol_0-phixpol_oo+phixpol_1)]);        
      elif degphi_0 eq degphi_oo then
        assert degphi_1 lt degphi_0;
        u := 1;
        vprint Shimura : Max([Abs(c) : c in Coefficients(phixpol_0-phixpol_oo-phixpol_1)]);
      elif degphi_0 eq degphi_1 then
        assert degphi_oo lt degphi_0;
        u := 1/(Coefficient(phixpol_0,degphi_oo)-Coefficient(phixpol_1,degphi_oo));
        vprint Shimura : Max([Abs(c) : c in Coefficients(u*phixpol_0-phixpol_oo-u*phixpol_1)]);        
      end if;
    end if;

    if Al eq "Newton" then
      assert precNewton gt 0;
      polsvec, u := TrianglePhiGenusZeroNewton(polsvec, u, Gamma, precNewton);

      phixpol_0 := &*[f[1]^f[2] : f in polsvec[1]];
      phixpol_1 := &*[f[1]^f[2] : f in polsvec[2]];
      phixpol_oo := &*[f[1]^f[2] : f in polsvec[3]];
    end if;

    phixnum := phixpol_0;
    phixden := phixpol_oo;
  end if;

  phixnum /:= LeadingCoefficient(phixnum);
  phixnum_seq := Eltseq(phixnum);
  phixden /:= LeadingCoefficient(phixden);
  phixden_seq := Eltseq(phixden);

  if justCC then
    return [* u, phixnum, phixden *];
  end if;

  if m eq 0 then
    sigma := DefiningPermutation(Gamma);
    m := #PassportRepresentatives(sigma : Pointed := true);
  end if;

  vprint Shimura : "Looking for coefficient to recognize number field...";  
  bl := false;
  cfs := Reverse([u] cat phixden_seq cat phixnum_seq);
  cfs_ind := 0;
  while not bl and cfs_ind lt #cfs do
    cfs_ind +:= 1;
    bl, K, v, conj, uCC := MakeK(cfs[cfs_ind], m);
  end while;
  if not bl then
    error "K not found; is the Galois orbit smaller than the passport size?  Try smaller m!";
  end if;
  Gamma`TriangleK := K;
  Gamma`TriangleKv := v;
  Gamma`TriangleKIsConjugated := conj;
  Gamma`TriangleKNumericalGenerator := uCC;

  vprint Shimura : "... found!", K;
  vprint Shimura : "Recognizing coefficients...";
  
  uK_seq, phixnumK_seq, phixdenK_seq := Explode(RecognizeOverK([[u],phixnum_seq,phixden_seq], K, v, conj));
  
  vprint Shimura : "...Coefficients recognized!";
  uK := uK_seq[1];
  Gamma`TriangleExactBelyiMapLeadingCoefficient := uK;
  Gamma`TriangleExactBelyiMapNumeratorCoefficients := phixnumK_seq;
  Gamma`TriangleExactBelyiMapDenominatorCoefficients := phixdenK_seq;

  Kig := PolynomialRing(K);
  phix := uK*(Kig!phixnumK_seq)/(Kig!phixdenK_seq);
  PP1 := Curve(ProjectiveSpace(PolynomialRing(K, 2)));
  KPP1<x> := FunctionField(PP1);
  phix := Evaluate(phix,x);
  Gamma`TriangleBelyiCurve := PP1;
  Gamma`TriangleBelyiMap := phix;
  /*
  num := Numerator(phix);
  den := Denominator(phix);
  lc_num := LeadingCoefficient(num)
  num := num/lc_num;
  lc_den := LeadingCoefficient(den);
  den := den/lc_den;
  lc := lc_num/lc_den;
  Gamma`TriangleExactBelyiMapLeadingCoefficient := lc;
  Gamma`TriangleExactBelyiMapNumeratorCoefficients := Coefficients(num);
  Gamma`TriangleExactBelyiMapDenominatorCoefficients := Coefficients(den);
  */

  return PP1, phix;
end intrinsic;

/*
// TODO genus zero rescaling for Galois orbit method
intrinsic TriangleRescalingFactorGenusZero(s::BelyiDBObject : rescale_ind := 0, num_bool := false) -> Any
  {Defines rescaling factor lambda in terms of coefficients in order to make coefficients algebraic.  Parameter rescale_inds forces lambda to be computed using given indices. num_bool indicates if ratio of numerator coefficients was used. Returns lambda, rescale index, and num_bool.}
  
  pass := s`BelyiDBPointedPassport;
  sigma := pass[1];
  Gamma := TriangleSubgroup(sigma);
  aut := #AutomorphismGroup(Gamma);
  // renormalize Theta by rescaling factor lambda
  lambdas := [];
  for s := 1 to 3 do
    for fv in polsvec[s] do
      for trycf := 0 to (Degree(fv[1]) div aut)-1 do
        a1 := Coefficient(fv[1],trycf*aut);
        a2 := Coefficient(fv[1],(trycf+1)*aut);
        if Abs(a1) gt eps and Abs(a2) gt eps then
          lambda := (a1/a2)^(1/aut);
          Append(~lambdas, [a1,a2,lambda]);
        end if;
      end for;
    end for;
  end for;
  return "";
end intrinsic;
*/

intrinsic TriangleGenusZeroFactorizationPattern(Gamma::GrpPSL2Tri) -> Any
{Factorization pattern of rational Belyi function.}
  require Genus(Gamma) eq 0 : "Only for genus zero gamma";

  fact := [];
  sigma := DefiningPermutation(Gamma);
  for i := 1 to 3 do
    sigmai := sigma[i];

    cyc := CycleDecomposition(sigmai);
    cyc_ord := Reverse(Sort(SetToSequence({#x : x in cyc})));
    cyc_reps := [ [] : c in cyc_ord ];
    for c in cyc do
      ind := Index(cyc_ord, #c);
      cyc_reps[ind] := Append(cyc_reps[ind],c[1]);
    end for;

    if i eq 1 then
      i1 := 1;
      while 1 notin cyc_reps[i1] do
        i1 +:= 1;
      end while;
      cyc_ord := [cyc_ord[i1]] cat cyc_ord[1..i1-1] cat cyc_ord[i1+1..#cyc_ord];
      cyc_reps := [cyc_reps[i1]] cat cyc_reps[1..i1-1] cat cyc_reps[i1+1..#cyc_reps];
    end if;

    Append(~fact, [<cyc_ord[i], cyc_reps[i]> : i in [1..#cyc_ord]]);
  end for;

  return fact;
end intrinsic;

intrinsic TrianglePhiGenusZeroEquations(Gamma::GrpPSL2Tri : WithInverses := true) -> Any
{System of equations for Gamma.}

  sigma := DefiningPermutation(Gamma);
  Ccyc := [CycleStructure(c) : c in sigma];

  // must ensure first one contains 1
  a := Order(sigma[1]);
  e := #CycleDecomposition(sigma[1])[1]; //length of cycle containing 1 in sigma0
  i := 1;
  while Ccyc[1][i][1] ne e do
    i +:= 1;
  end while;
  Ccyc[1] := [Ccyc[1][i]] cat Ccyc[1][1..i-1] cat Ccyc[1][i+1..#Ccyc[1]];

  require Ccyc[1][1][1] ge 2 and Ccyc[1][1][1] ne a : "Need cycle containing 1 in sigma_0 to have length >= 2 and < a, for convenience";

  // Declare variables
  numVars := &+[&+[c[2] : c in Ccyc[i]] : i in [1..3]]; //Sum of number of cycles in perm'ns in sigma
  numVarsXtra := &+[#c : c in Ccyc];  //Sum of number of cycles of distinct length in sigma

  if WithInverses then
    Pa<[a]> := PolynomialRing(Rationals(), numVars + numVarsXtra+1);
  else
    Pa<[a]> := PolynomialRing(Rationals(), numVars);
  end if;
  Pt<ta> := PolynomialRing(Pa);

  // Build up the generic function j of t with the given cycle structure
  jFactors := [Pt | 1, 1, 1];
  cnt := 1;
  constCoeffs := [numVars];
  normeqij := [];
  for i := 1 to 3 do
    for j := 1 to #Ccyc[i] do
      c := Ccyc[i][j];
      if i eq 1 and j eq 1 then
        jFactors[i] *:= Polynomial([0] cat a[cnt..cnt+c[2]-2] cat [1])^c[1];
        if c[2] gt 1 then
          Append(~constCoeffs, cnt);
          cnt +:= c[2]-1;
        end if;
        normeqij cat:= [[i,j,k,cnt+k] : k in [1..c[2]-2]];
      else
        jFactors[i] *:= Polynomial(a[cnt..cnt+c[2]-1] cat [1])^c[1];
        Append(~constCoeffs, cnt);
        if c[2] eq 1 then
          Append(~normeqij, [i,j,-1,cnt]);
        else
          normeqij cat:= [[i,j,k,cnt+k] : k in [0..c[2]-2]];
        end if;
        cnt +:= c[2];
      end if;
    end for;
  end for;
  // Constant factors
  jFactors[1] *:= a[numVars];
  jFactors[2] *:= a[numVars]-1;

  // Set up equations
  jSolveNum := jFactors[1]-jFactors[2]-jFactors[3];

  aa := Ccyc[1][1][1];
  p0 := Coefficient(jFactors[1],aa);
  p1 := Coefficient(jFactors[1],aa+1);
  q0 := Coefficient(jFactors[3],0);
  q1 := Coefficient(jFactors[3],1);

  normeq := q1*p0 - q0*p1;
  for c in constCoeffs do
    while IsDivisibleBy(normeq, a[c]) do
      normeq div:= a[c];
    end while;
  end for;
  normeqs := [normeq, a[normeqij[1][4]] - a[normeqij[1][4]+1]];

  cfs := Coefficients(jSolveNum);
     // cat &cat[Coefficients(Derivative(jSolveNum,s)) : s in [1..Degree(jSolveNum)]];
  for i := 1 to #cfs do
    cfs[i] /:= Gcd(ChangeUniverse(Coefficients(cfs[i]),Integers()));
  end for;

  if WithInverses then
    inveqs := [a[constCoeffs[c]]*a[numVars+c] - 1 : c in [1..#constCoeffs]];
    I := ideal<Pa | normeqs cat inveqs cat cfs>;
  else
    I := ideal<Pa | normeqs cat cfs>;
  end if;

  return I, jFactors, constCoeffs, normeqij;
end intrinsic;

intrinsic TrianglePhiGenusZeroNewton(polsvec::SeqEnum[SeqEnum[Tup]], u::FldComElt, Gamma::GrpPSL2Tri, precNewton::RngIntElt) -> Any
{Newton iterate from existing factorization to desired prec.}
  require Genus(Gamma) eq 0 : "Only for genus zero gamma";

  CC := Parent(u);
  prec := Precision(CC);
  eps := 10^(-Precision(CC)/2);

  polsvecsc := polsvec;

  I, jFactors, _, normeqij := TrianglePhiGenusZeroEquations(Gamma : WithInverses := false);

  nij := 0;
  found_lambda := false;
  lambdas := [];
  // There's a problem if the normalization constraint sets two adjacent coefficients
  // equal and one of them is zero, forcing degeneration.
  repeat
    nij +:= 1;
    nm := normeqij[nij];
    i := nm[1];
    j := nm[2];
    k := nm[3];
    cnt := nm[4];
    if k eq -1 then
      a1 := Coefficient(polsvecsc[i][j][1],0);
      a2 := 1; 
    else
      a1 := Coefficient(polsvecsc[i][j][1],k);
      a2 := Coefficient(polsvecsc[i][j][1],k+1);
    end if;
    if Abs(a1) gt eps and Abs(a2) gt eps then
      lambda := a1/a2;
      Append(~lambdas, [* lambda, a1, a2, nij *]);
      found_lambda := true;
    end if;
  until nij eq #normeqij;
  vprintf Shimura : "lambdas: %o... \n", [RealField(6)!Abs(lambda[1]) : lambda in lambdas];
  
  if not found_lambda then
    error "Unable to normalize by setting two adjacent coefficients equal, try with a different algorithm";
  end if;
  
  lambdadat := lambdas[#lambdas];
  lambda := lambdadat[1];
  nm := normeqij[lambdadat[4]];
  k := nm[3];
  cnt := nm[4];
  vprintf Shimura : "Taking lambda = %o = %o/%o... \n", ComplexField(6)!lambda, ComplexField(6)!lambdadat[2], ComplexField(6)!lambdadat[3];
  Gamma`TriangleRescalingFactor := lambda;
  Igens := Generators(I);
  Pa<[a]> := Universe(Igens);
  if k eq -1 then
    Igens[2] := a[cnt]-1;
  else
    Igens[2] := a[cnt]-a[cnt+1];
  end if;
  I := ideal<Pa | Igens>;

  _<xCC> := Parent(polsvecsc[1][1][1]);

  solvec := [];
  for i := 1 to 3 do
    for j := 1 to #polsvecsc[i] do
      polsvecsc[i][j][1] := Evaluate(polsvecsc[i][j][1], lambda*xCC)/lambda^Degree(polsvecsc[i][j][1]);
      if i eq 1 and j eq 1 then
        solvec cat:= Coefficients(polsvecsc[i][j][1])[2..Degree(polsvecsc[i][j][1])];
      else
        solvec cat:= Coefficients(polsvecsc[i][j][1])[1..Degree(polsvecsc[i][j][1])];
      end if;
    end for;
  end for;
  assert &+[Degree(f[1])*f[2] : f in polsvecsc[1]] eq &+[Degree(f[1])*f[2] : f in polsvecsc[3]];
  solvec cat:= [u];
  solvec := Vector(solvec);

  dd := Ncols(solvec);
  cfs := Generators(I)[1..dd];

  precstart := prec;
  itercnt := 0;
  while itercnt lt 50 do
    itercnt +:= 1;
    solvec := ChangeRing(solvec, ComplexField(prec));
    fsol := [-Evaluate(P,Eltseq(solvec)) : P in cfs];
    err := RealField()!Max([Abs(fs) : fs in fsol]);

    if prec ge precNewton then
      prec +:= Ceiling(1/10*precNewton);
    else
      prec := Max([precstart,Min([precNewton,Ceiling(11/10*prec)]),Min([precNewton,Ceiling(-2*Log(err)/Log(10))])]);
    end if;

    vprintf Shimura : "%o: err = %o, prec = %o... ", itercnt, RealField(6)!err, prec;
    if prec ge precNewton and err lt 10^(-precNewton+Log(precNewton)) then
      vprintf Shimura : "\n";
      break;
    end if;
    J := Matrix([[Evaluate(Derivative(P,Parent(P).i),Eltseq(solvec)) : P in cfs] : i in [1..dd]]);
    Q, L := QLDecomposition(J);
    w := (Vector(fsol)*(L^-1))*Conjugate(Transpose(Q));   // this is ridiculous, shouldn't have to compute an inverse
    // In QR, R = Transpose(A)*J.  What is the correct thing for QL? L2LA
    // w := Vector(fsol)*NumericalPseudoinverse(J);      // why so slow?
    
    vprintf Shimura : "Norm(w) = %o\n", RealField(6)!Sqrt(&+[Abs(ww)^2 : ww in Eltseq(w)]);
    solvec +:= w;
  end while;
  if itercnt eq 50 then
    error "Newton didn't converge or something?";
  end if;

  fact := TriangleGenusZeroFactorizationPattern(Gamma);

  solvec := Eltseq(ChangeRing(solvec,ComplexField(precNewton)));

  polsvecsc := [];
  cnt := 1;
  for i := 1 to 3 do
    polv := [];
    for j := 1 to #fact[i] do
      if i eq 1 and j eq 1 then
        Append(~polv, <Polynomial([0] cat solvec[cnt..cnt+#fact[i][j][2]-2] cat [1]), fact[i][j][1]>);
        cnt +:= #fact[i][j][2]-1;
      else
        Append(~polv, <Polynomial(solvec[cnt..cnt+#fact[i][j][2]-1] cat [1]), fact[i][j][1]>);
        cnt +:= #fact[i][j][2];
      end if;
    end for;
    Append(~polsvecsc, polv);
  end for;

  return polsvecsc, solvec[#solvec];
end intrinsic;
