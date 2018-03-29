/*
---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------
                       ,@.                                  @@@@
 :@@@@@@@@             ,@.                                  ;@@@
 :@`.@,.@@                                                    :@
 :@  @. @@  @@@ @@@   @@@#     #@@@@#   @@'@@@+    @@@@'@@`   :@      ;@@@@     @@@@@@
 .@  @. @#  @@@@@'@+  @@@#     @@+'@@,  @@@@'@@`  @@@'@@@@    :@     @@@'+@@   #@@'@@@
     @.      #@@        @#      ;@@@@;   @,   @: ,@`   @@     :@     @#    @@  #@:`  :
     @.      #@         @#     @@@@@@;   @,   @: +@    +@     :@    `@@@@@@@@   #@@@@.
     @.      #@         @#    +@    @;   @,   @: ,@    @@     :@     @;        +    '@
   @@@@@`  ,@@@@@@   #@@@@@@. '@@'@@@@' @@@` @@@  @@@'@@@   @@@@@@@  @@@''@@@  @@@''@@
   @@@@@:  +@@@@@@   @@@@@@@'  @@@@`@@@ @@@; @@@`  @@@@'@  .@@@@@@@   +@@@@@.  @@@@@@
                                                       #@
                                                   +@@@@@
                                                   @@@@'
---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------
*/


/*
----------------------------------------------------------------------------
----------------------------------------------------------------------------
Group Presentation
Input:
	triangle subgroup Gamma
Output:
	Return: abstract group underlying Gamma
----------------------------------------------------------------------------
*/

function MyMultiplicativeOrder(g,Delta);
  // Computes multiplicative order in a triangle group; apparently cannot use
  // MultiplicativeOrder because it computes order in B^* not B^*/F^*.
  
  m := Lcm(Signature(Delta)[2]);
  mults := [d : d in Divisors(m) | IsScalar(g^d)];
  if #mults eq 0 then
    return 0;
  else
    return Min(mults);
  end if;
end function;

intrinsic InternalTriangleGroupPresentation(Gamma::GrpPSL2) -> GrpFP, Map, Map
  {Returns a presentation U for the triangle subgroup Gamma,
   a map U -> Gamma, and a map U -> BaseRing(Gamma).}

  require IsTriangleSubgroup(Gamma) : "Only for triangle groups";

  if IsTriangleGroup(Gamma) then
    return Gamma`TriangleGroup, Gamma`TriangleGroupMap, Gamma`TriangleGroupMapExact;
  end if;

  // Triangle subgroup--need to compute cosets and side pairings.

  alphas, _, sidepairing_full := TriangleCosetRepresentatives(Gamma);
  // get rid of inverses
  sidepairing := [];
  for s in sidepairing_full do
    isnew := true;
    for t in sidepairing do
      if IsScalar(Quaternion(s[1]*t[1])) or IsScalar(Quaternion(s[1]^-1*t[1])) then
        isnew := false;
        break t;
      end if;
    end for;
    if isnew then
      Append(~sidepairing, s);
    end if;
  end for;
  // or could have required s[2][1] le s[3][1] and made a choice when equal

  DD := TriangleUnitDisc(Gamma);
  prec := DD`prec;
  Delta := ContainingTriangleGroup(Gamma);
  FD := FundamentalDomain(Delta, DD);
  ws := [FD[1], FD[3], FD[2]];

  sigma := DefiningPermutation(Gamma);
  sidepairs := [s[1] : s in sidepairing] cat [s[1]^-1 : s in sidepairing];
  sidesind := [1..#sidepairing] cat [-i : i in [1..#sidepairing]];
  words := [];
  for i := 1 to 3 do
    cyci := CycleDecomposition(sigma[i]);
    for c in cyci do
      w := [];
      for j := 1 to #c do
        alphacj := alphas[c[j]];
        alphacj1 := alphas[c[(j mod #c)+1]];
        if Abs(alphacj*ws[i] - alphacj1*ws[i]) lt 10^(-prec+2) then
          continue;
        end if;
        err, s := Min([Abs((side*alphacj)*ws[i] - alphacj1*ws[i]) : side in sidepairs]);
        if err gt 10^(-prec+2) then
          assert i eq 3;
          // fundamental domain split up the two half-triangles
          found := false;
          for r, s in [1..#sidepairs] do
            if sidesind[r]+sidesind[s] eq 0 then // inverses
              continue;
            end if;
            if Abs((sidepairs[s]*sidepairs[r]*alphacj)*ws[i] - alphacj1*ws[i]) lt 10^(-prec+2) then
              found := true;
              Append(~w, sidesind[r]);
              Append(~w, sidesind[s]);
              break r;
            end if;
          end for;
        else
          Append(~w, sidesind[s]);
        end if;
      end for;
      if not IsEmpty(w) then
        Append(~words, w);
      end if;
    end for;
  end for;

  for i := 1 to #words do
    w := &*[ sidepairing[Abs(s)][1]^Sign(s) : s in Reverse(words[i])];
    wpow := w;
    e := 1;
    while not IsScalar(Quaternion(wpow)) do
      wpow *:= w;
      e +:= 1;
    end while;
    words[i] := &cat[ words[i] : j in [1..e]];
  end for;

  vprintf Shimura : "Cycles (with trivial stabilizers):\n%o\n", words;

  gammagens := [s[1] : s in sidepairing];
  orders := [MyMultiplicativeOrder(Quaternion(g),Delta) : g in gammagens];

  vprintf Shimura : "Generators with orders:\n";
  for i := 1 to #gammagens do
    vprintf Shimura : "Generator %o = %o, has order %o\n", i, gammagens[i], orders[i];
  end for;
  vprintf Shimura : "\n";

  Gfree := FreeGroup(#gammagens);
  U := quo<Gfree | [Gfree.i^orders[i] : i in [1..#orders]] cat
                   [Gfree!w : w in words]>;

  vprintf Shimura : "Group is %o\n\n", U;

  Delta := ContainingTriangleGroup(Gamma);
  m := map<U -> Delta | x :-> &*([Id(Delta)] cat [ gammagens[Abs(s)]^Sign(s) : s in Eltseq(x)])>;

  P := TietzeProcess(U);
  SimplifyPresentation(~P);
  U, f := Group(P);
  m := f^(-1)*m;

  vprintf Shimura : "Simplified group is %o\n\n", U;

  Gamma`TriangleGroupPresentation := U;
  Gamma`TriangleGroupPresentationMap := m;

  return U, m;
end intrinsic;

/*
----------------------------------------------------------------------------
----------------------------------------------------------------------------
Delta Generators Embedding
Input:
	triangle group Delta
Output:
	Return: a sequence of three exact matrices, embeddings
		of delta_a, delta_b, and delta_c into PSL(2,RR).
----------------------------------------------------------------------------
*/

intrinsic InternalTriangleGroupMapExact(Delta::GrpPSL2 : Simplify := 1) -> SeqEnum
  {Returns a quaternionic representation for Delta.}

  require IsTriangleGroup(Delta) : "Must be triangle group";

  a,b,c := Explode(DefiningABC(Delta));

	m := Lcm([a,b,c]);
	K<z2m> := CyclotomicField(2*m);
  z2a := z2m^(m div a);
  z2b := z2m^(m div b);
  z2c := z2m^(m div c);
  l2a := z2a+1/z2a;
  l2b := z2b+1/z2b;
  l2c := z2c+1/z2c;
  if Simplify ge 1 then
  	F := sub<K | [l2a,l2b,l2c]>;
  	if F cmpeq Rationals() then
  	  ZF := Integers();
	  else
  	  OF := EquationOrder(F);
  	  ZF := MaximalOrder(OF : Ramification := PrimeDivisors(m));
	  _, ZF := OptimizedRepresentation(ZF);
	  end if;
  	F<w> := NumberField(ZF);
  else
    F<w> := sub<K | [z2m+1/z2m]>;
  end if;
	l2a := F!l2a;
	l2b := F!l2b;
	l2c := F!l2c;

  if Simplify ge 1 then
    E := sub<F | [l2a^2, l2b^2, l2c^2, l2a*l2b*l2c]>;
  	if E cmpeq Rationals() then
  	  ZE := Integers();
	  else
  	  OE := EquationOrder(E);
	    ZE := MaximalOrder(OE : Ramification := PrimeDivisors(m));
	    bl, ZEop := OptimizedRepresentation(ZE);
	    if bl then
	      ZE := ZEop;
	    end if;
	  end if;
	  E := NumberField(ZE);
	else
	  E := F;
  end if;

  if E ne Rationals() then
    v := E.1;
    if Simplify ge 1 then
      Eop, mEop := OptimizedRepresentation(E);
    else
      Eop := E;
      mEop := hom<Eop -> E | E.1>;
    end if;
	  la := mEop(E!(l2a^2));
  	lb := mEop(E!(l2b^2));
  	lc := mEop(E!(l2c^2));
  else
    v := E!1;
    la := E!(l2a^2);
    lb := E!(l2b^2);
    lc := E!(l2c^2);
    Eop := E;
    mEop := hom<Eop -> E | >;
  end if;

  if la eq 0 then
		Ffree<fa,fb,fc> := FreeAlgebra(Eop, 3);
		A<fa,fb,fc> := quo<Ffree |
		fa^2 + lb*lc,
		fb^2 - lb*fb + lb,
		fc^2 - lc*fc + lc,
		fa*fb + lb*lc*(1-fc/lc),
		fb*fc - fa,
		fc*fa + lb*lc*(1-fb/lb),
		fb*fa - lb*fa + lb*fc,
		fc*fb - lc*fb - lb*fc + fa + lb*lc,
    fa*fc - lc*fa + lc*fb>;
  elif lb eq 0 then
		Ffree<fa,fb,fc> := FreeAlgebra(Eop, 3);
		A<fa,fb,fc> := quo<Ffree |
		fa^2 - la*fa + la,
		fb^2 + la*lc,
		fc^2 - lc*fc + lc,
		fa*fb + la*lc*(1-fc/lc),
		fb*fc + la*lc*(1-fa/la),
		fc*fa - fb,
    fb*fa - la*fb + la*fc,
		fc*fb - lc*fb + lc*fa,
		fa*fc - la*fc - lc*fa + fb + lc*la>;
  elif lc eq 0 then
		Ffree<fa,fb,fc> := FreeAlgebra(Eop, 3);
		A<fa,fb,fc> := quo<Ffree |
		fa^2 - la*fa + la,
		fb^2 - lb*fb + lb,
		fc^2 + la*lb,
		fa*fb - fc,
		fb*fc + la*lb*(1-fa/la),
		fc*fa + la*lb*(1-fb/lb),
		fb*fa - lb*fa - la*fb + fc + la*lb,
    fc*fb - lb*fc + lb*fa,
		fa*fc - la*fc + la*fb>;
  else
  	l2abc := mEop(E!(l2a*l2b*l2c));
		Ffree<fa,fb,fc> := FreeAlgebra(Eop, 3);
		A<fa,fb,fc> := quo<Ffree |
		fa^2 - la*fa + la,
		fb^2 - lb*fb + lb,
		fc^2 - lc*fc + lc,
		fa*fb + l2abc*(1-fc/lc),
		fb*fc + l2abc*(1-fa/la),
		fc*fa + l2abc*(1-fb/lb),
		fb*fa - lb*fa - la*fb + l2abc/lc*fc + la*lb,
		fc*fb - lc*fb - lb*fc + l2abc/la*fa + lb*lc,
		fa*fc - la*fc - lc*fa + l2abc/lb*fb + lc*la>;
  end if;

	Aass, mass := Algebra(A);

	bl, Aquat, mquat := IsQuaternionAlgebra(Aass);
	assert bl;
	aa, bb := StandardForm(Aquat);

  if Simplify ge 2 then
    ZEop := Integers(Eop);
    _, mCl := ClassGroup(ZEop : Proof := "GRH");

    if ZEop cmpeq Integers() then
      aafact := [<pp[1], pp[2]> : pp in Factorization(Numerator(aa))] cat
                [<pp[1], -pp[2]> : pp in Factorization(Denominator(aa))];
      bbfact := [<pp[1], pp[2]> : pp in Factorization(Numerator(bb))] cat
                [<pp[1], -pp[2]> : pp in Factorization(Denominator(bb))];
    else
    	aafact := Factorization(aa*ZEop);
    	bbfact := Factorization(bb*ZEop);
    end if;

    if #aafact gt 0 then
      aaden := &*[pp[1]^Floor(pp[2]/2) : pp in aafact];
      aaden := aaden^-1;

      if ZEop cmpeq Integers() then
        aa_den := aaden;
      else
        aa0 := mCl((aaden^-1)@@mCl);
        aaden *:= aa0;
        _, aa_den := IsPrincipal(aaden);
      end if;
    else
      aa_den := 1;
    end if;
    if #bbfact gt 0 then
      bbden := &*[pp[1]^Floor(pp[2]/2) : pp in bbfact];
      bbden := bbden^-1;

      if ZEop cmpeq Integers() then
        bb_den := bbden;
      else
        bb0 := mCl((bbden^-1)@@mCl);
        bbden *:= bb0;
        _, bb_den := IsPrincipal(bbden);
      end if;
    else
      bb_den := 1;
    end if;

  	aa_int := aa*aa_den^2;
  	bb_int := bb*bb_den^2;
  	Aquat_int := QuaternionAlgebra<Eop | aa_int, bb_int>;
  	mquat_int := hom<Aquat -> Aquat_int | 1, Aquat_int.1/aa_den,
  	    Aquat_int.2/bb_den, Aquat_int.3/(aa_den*bb_den)>;
    Aquat := Aquat_int;
    mquat := mquat*mquat_int;

  	Aquatop, mquatop := OptimizedRepresentation(Aquat);

  	faop := mquatop(mquat(mass(fa)));
  	fbop := mquatop(mquat(mass(fb)));
  	fcop := mquatop(mquat(mass(fc)));
  end if;

  Aquatop := Aquat;
	faop := mquat(mass(fa));
	fbop := mquat(mass(fb));
	fcop := mquat(mass(fc));

	Delta`BaseRing := Aquatop;
	Lambda := Aquatop;

	Delta`TriangleGroupMapExact := Delta`TriangleGroupMap^-1*
	                      map<Delta`TriangleGroup -> Lambda |
                  x :-> &*([Lambda!1] cat [[faop,fbop,fcop][Abs(s)]^Sign(s) : s in Eltseq(x)])>;

	return Delta`TriangleGroupMapExact;
end intrinsic;


/*
----------------------------------------------------------------------------
----------------------------------------------------------------------------
Delta Generators Embedding
Input:
	triangle group Delta
Output:
	Return: matrix embedding of Delta(a,b,c) into PSL_2(RR)
		**delta_c has not been full tested**
----------------------------------------------------------------------------
*/

intrinsic InternalTriangleMatrixEmbeddingMap(Delta::GrpPSL2 : Precision := 0) -> SeqEnum
  {Returns a sequence of matrices giving the embedding Delta(a,b,c) in PSL_2(RR).}

  require IsTriangleGroup(Delta) : "Must be triangle group";

  if Precision eq 0 then
    RR := RealField();
  else
    RR := RealField(Precision);
  end if;

  a,b,c := Explode(DefiningABC(Delta));

  pi := Pi(RR);
  cosa := Cos(pi/a);
  cosb := Cos(pi/b);
  cosc := Cos(pi/c);
  sina := Sin(pi/a);
  sinb := Sin(pi/b);
  sinc := Sin(pi/c);

  l := (cosa*cosb+cosc)/(sina*sinb);
  t := l+Sqrt(l^2-1);

  da := Matrix([[cosa,sina],[-sina,cosa]]);
  db := Matrix([[cosb,t*sinb],[-sinb/t,cosb]]);
  dc := (da*db)^-1;
// dc := Matrix([[cosa*cosb-(1/t)*sina*sinb, -t*cosa*sinb-cosb*sina],
//               [cosb*sina+(1/t)*cosa*sinb, cosa*cosb - t*sina*sinb]]);

  Delta`TriangleMatrixEmbeddingMap := Delta`TriangleGroupMap^-1*
	                      map<Delta`TriangleGroup -> Parent(da) |
                  x :-> &*([Parent(da)!1] cat [[da,db,dc][Abs(s)]^Sign(s) : s in Eltseq(x)])>;
  Delta`TriangleMatrixEmbeddingMapPrec := Precision;

  CC<I> := ComplexField(RR);

  wawb := HackobjCreateRaw(GrpPSL2Elt);
  wawb`Parent := Delta;
  A := Matrix([[ t+1, -t+1 ], [ -t+1, t+1 ]]);
  wawb`Element := A;
  wawb`MatrixD := A;
  wawb`MatrixDCenter := UpperHalfPlane()!I;
  Delta`TriangleSwapOriginMap := wawb;
  Delta`TriangleSwapOriginMapPrec := Precision;

  return Delta`TriangleMatrixEmbeddingMap;
end intrinsic;

intrinsic InternalTriangleSwapOriginMap(Delta::GrpPSL2 : Precision := 0) -> Any
  {Returns the matrix corresponding to the linear fractional transformation
   mapping the unit disc centered at p = z_a = i to the unit disc centered
   at p = z_b = t*i.}

  require IsTriangleGroup(Delta) : "Must be triangle group";

  if not assigned Delta`TriangleSwapOriginMap or
    (Precision ne 0 and Delta`TriangleSwapOriginMapPrec ne Precision) then
    _ := InternalTriangleMatrixEmbeddingMap(Delta : Precision := Precision);
  end if;

  return Delta`TriangleSwapOriginMap;
end intrinsic;

intrinsic TriangleUnitDisc(Gamma::GrpPSL2 : Precision := 0) -> SpcHyd
  {Returns the unit disc centered at z_a = I with given precision.}

  Delta := ContainingTriangleGroup(Gamma);

  if assigned Delta`TriangleUnitDisc then
    if Precision eq 0 or Delta`TriangleUnitDisc`prec eq Precision then
      return Delta`TriangleUnitDisc;
    end if;
  end if;

  if Precision eq 0 then
    CC<I> := ComplexField();
  else
    CC<I> := ComplexField(Precision);
  end if;
  D := UnitDisc( : Center := UpperHalfPlane()!I, Precision := Precision);

  _ := InternalTriangleMatrixEmbeddingMap(Delta : Precision := Precision);

  Delta`TriangleUnitDisc := D;
  return D;
end intrinsic;

/*
----------------------------------------------------------------------------
----------------------------------------------------------------------------
Gamma Matrix Embedding
Input:
	g an element of a triangle subgroup Gamma
Output:
	Return: matrix embedding of Gamma into PSL_2(RR)
----------------------------------------------------------------------------
*/

intrinsic InternalTriangleMatrixRepresentation(g::GrpPSL2Elt : Precision := 0) -> GrpMatElt
  {Returns a matrix form of g in the upper half-plane, optionally with specified precision.}

  Gamma := Parent(g);
  Delta := ContainingTriangleGroup(Gamma);

  if not assigned Delta`TriangleMatrixEmbeddingMap or
    (Precision ne 0 and Delta`TriangleMatrixEmbeddingMapPrec ne Precision) then
    Phi := InternalTriangleMatrixEmbeddingMap(Delta : Precision := Precision);
  else
    Phi := Delta`TriangleMatrixEmbeddingMap;
  end if;

  return Phi(g`Element);
end intrinsic;



/*
----------------------------------------------------------------------------
----------------------------------------------------------------------------
Fundamental Domain
Input:
	triangle subgroup Delta
Output:
	return: sequence of sequences consisting each the four vertices for a
	fundamental domain for Delta(a,b,c) in a list: [z_a, z_c, z_b, z_c^*],
	working in the upper half-plane, hit by the cosets of Gamma in Delta.
	z_a = i for all triples, and z_b = ti for some real number t. z_c is
	always in the first quadrant.
----------------------------------------------------------------------------
*/

intrinsic InternalTriangleFDH(Gamma::GrpPSL2, HH::SpcHyp : Precision := 0) -> SeqEnum
  {Returns the fundamental domain for a triangle subgroup Gamma.}

	a,b,c := Explode(DefiningABC(Gamma));

  Delta := ContainingTriangleGroup(Gamma);

  if Precision eq 0 then
    if assigned Delta`TriangleUnitDisc then
      RR := RealField(Delta`TriangleUnitDisc`prec);
    else
      RR := RealField();
    end if;
  else
    RR := RealField(Precision);
  end if;

  if assigned Gamma`ShimFDDisc and Precision eq 0 then
    return [DiscToPlane(HH, w) : w in Gamma`ShimFDDisc];
  elif assigned Gamma`TriangleFD and Precision eq 0 then
    return Gamma`TriangleFD;
  end if;

  Delta := ContainingTriangleGroup(Gamma);
  if assigned Delta`TriangleFD and Precision eq 0 then
    V := Delta`TriangleFD;
  else
    // See explicit formulas and picture in KMNSV-13
	  l := (Cos(Pi(RR)/a)*Cos(Pi(RR)/b)+Cos(Pi(RR)/c))/(Sin(Pi(RR)/a)*Sin(Pi(RR)/b));
	  t := l+Sqrt(l^2-1);
	  x := ((t^2)-1)/(2*(Cot(Pi(RR)/a) + t*Cot(Pi(RR)/b)));
	  y := Sqrt(Cosec(Pi(RR)/a)^2 - (x - Cot(Pi(RR)/a))^2);
	  I := Sqrt(RR!-1);

    V := [HH | I, x+y*I, t*I, -x+y*I];
  end if;

  if IsTriangleGroup(Gamma) then
    return V;
  else
    // This is OK for now, but to be consistent with what else is being produced,
    // it should give the vertices in counterclockwise order by their argument.
    return &cat[[delta*v : v in V] : delta in TriangleCosetRepresentatives(Gamma)];
  end if;
end intrinsic;
