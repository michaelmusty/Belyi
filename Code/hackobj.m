//====================
//
// TRIANGLE GROUPS
//
// This file contains the basic structures and types for triangle groups.
//
// KMNSV-351, June 2013
//
//====================

declare type GrpPSL2Tri[GrpPSL2Elt]: GrpPSL2;  
  // meaningless, since inheritance is not implemented; might as well be a new type

declare attributes GrpPSL2Tri:  // = Gamma, a Fuchsian group

  UnderlyingGrpPSL2, 
                    // Underling GrpPSL2 (inheritance is broken)
  
  TriangleWhichCoset,
                    // index of white vertex for each coset
  TriangleDDs,      // unit disks centered at white vertices
  TrianglePowserBases,
                    // stored output from TrianglePowerSeriesBasis
  TriangleTheta,    // Theta for normalization
  TriangleK,        // Number field
  TriangleKv,       // Embedding
  TriangleKIsConjugated,
                    // if conjugated
  TriangleKNumericalGenerator,
                    // complex number used to recognize number field
  TriangleBelyiCurve,
                    // Algebraic curve representing the Riemann surface Gamma\H
  TriangleBelyiMap, // Equation for Belyi map as rational function
  TriangleSigma,    // = DefiningPermutation(Gamma), permutation defining the (sub)group Gamma.
                    // Empty list [] if full triangle group
  TriangleABC,      // = DefiningABC(Gamma), the orders a,b,c defining the (sub)group.
  TriangleD,        // = IndexDegree(Gamma), index of the group in its associated triangle group.

  TriangleParent,   // = ContainingTriangleGroup(Gamma), the containing triangle group.
  TriangleGroup,    // = Group(Gamma), underlying abstract finitely-presented group
  TriangleGroupMap, // = map Group(Gamma) -> Gamma
  TriangleGroupMapExact,
                    // = map Group(Gamma) -> quaternion algebra
  TriangleGroupPresentation,
                    // = FPGroup
  TriangleGroupPresentationMap,
                    // map FPGroup -> Gamma

  TrianglePi,       // = pi : Delta(a,b,c) -> S_d corresponding to Sigma,
                    // i.e., pi : Group(TriangleParent) -> Universe(TriangleSigma)

  TriangleUnitDisc, // Canonical unit disc, with center at z_a = I
  TriangleFD,       // = FundamentalDomain(Gamma), a fundamental domain for Gamma in the
                    // upper half-plane.

  TriangleSwapOriginMap, TriangleSwapOriginMapPrec,
                    // = InternalTriangleSwapOriginMap(Gamma), the matrix
                    // corresponding to the linear fractional transformation
                    // mapping the unit disc centered at p = z_a = i to the unit
                    // disc centered at p = z_b = t*i

  TriangleMatrixEmbeddingMap, TriangleMatrixEmbeddingMapPrec,
                    // = InternalTriangleMatrixEmbeddingMap(Delta) and its precision
                    // defined for triangle groups

  TriangleCosets, TriangleCosetGraph, TriangleSidePairing,
                    // = CosetRepresentatives(Gamma), cosets and coset graph of
                    // Gamma in Delta

  TriangleDessin,
                    // = TriangleDrawDessin(Gamma,prec), latex file to draw a conformal dessin
                    // for Gamma

                    // attributes previously included in BelyiDB objects

  TriangleNumericalPrecision,
                    // Precision of all computed numerical data

  TriangleNumericalEpsilon,
                    // Bound for deciding machine zeroes.  10^(-prec/2) by default?

  TriangleNumericalCurveInvariants,
                    // Numerical approximation for curve invariant(s)
                    // e.g., j-invariant for elliptic curves
  
  TriangleNumericalCurveCoefficients,
                    // Numerical approximation for curve coefficients

  TriangleNumericalBelyiMapLeadingCoefficient,
                    // Numerical approximation for leading coefficient of Belyi map

  TriangleNumericalBelyiMapNumeratorCoefficients,
                    // Numerical approximation for coefficients of numerator of Belyi map

  TriangleNumericalBelyiMapDenominatorCoefficients,
                    // Numerical approximation for coefficients of denominator of Belyi map
  TriangleRescalingFactor, // rescaling factor to make coefficients algebraic

  // exact versions of the above, i.e., now recognized as elements of a number field
  // need to modify galoisorbits.m and wherever we use MakeK to assign these attributes
  TriangleExactCurveInvariants,
  TriangleExactCurveCoefficients,
  TriangleExactBelyiMapLeadingCoefficient,
  TriangleExactBelyiMapNumeratorCoefficients,
  TriangleExactBelyiMapDenominatorCoefficients,
  TriangleKMinPoly,
                    // min poly for number field
  TriangleRiemannRochParameters, // [s,t] s and t: numerator in L(too), denominator in L((s+t)oo)

  /*
  MISC
  */
  TriangleNewtonHyperellipticLeadingCoefficient,
  TriangleIsHyperelliptic; // Is Gamma hyperelliptic? (with genus gt 2)





intrinsic 'eq'(Gamma1::GrpPSL2Tri, Gamma2::GrpPSL2Tri) -> BoolElt
  {Returns true if Gamma1 eq Gamma2.}

  return DefiningABC(Gamma1) eq DefiningABC(Gamma2) and
         DefiningPermutation(Gamma1) eq DefiningPermutation(Gamma2);
end intrinsic;

intrinsic Print(Gamma::GrpPSL2Tri) 
  {Print Gamma.}

  if Gamma`TriangleD gt 1 then
    printf "Subgroup of index d = %o defined by permutation\n%o\nof ", 
       IndexDegree(Gamma), DefiningPermutation(Gamma);
  end if;
  a,b,c := Explode(DefiningABC(Gamma));
  printf "Triangle group Delta(%o,%o,%o)", a,b,c; 
end intrinsic;

intrinsic IsTriangleGroup(Gamma::GrpPSL2Tri) -> BoolElt
  {Returns true if Gamma is a (full) triangle group.}

  return Gamma`TriangleD eq 1;
end intrinsic;

intrinsic DefiningPermutation(Gamma::GrpPSL2Tri) -> BoolElt
  {Returns the permutation defining a triangle subgroup Gamma.
   Returns the empty list if Gamma is the full triangle group.}

  return Gamma`TriangleSigma;
end intrinsic;

intrinsic DefiningABC(Gamma::GrpPSL2Tri) -> BoolElt
  {Returns the parameters a,b,c associated to the triangle group Delta
   containing Gamma.}

  return Gamma`TriangleABC;
end intrinsic;

intrinsic IndexDegree(Gamma::GrpPSL2Tri) -> BoolElt
  {Index of Gamma in its associated triangle group.}

  return Gamma`TriangleD;
end intrinsic;

intrinsic DefiningPermutationRepresentation(Gamma::GrpPSL2Tri) -> Map
  {Returns the permutation representation defining Gamma.
   Returns the trivial representation if Gamma is the full triangle group.}

  if IsTriangleGroup(Gamma) then
    return map<Gamma -> SymmetricGroup(1) | x :-> (1) >;
  else
    return Gamma`TrianglePi;
  end if;
end intrinsic;

intrinsic TriangleGroup(a::RngIntElt, b::RngIntElt, c::RngIntElt : Simplify := 1) -> GrpPSL2Tri
  {Creates the triangle group Delta(a,b,c).}

  require a ge 2 and b ge 2 and c ge 2 : "Must have a,b,c >= 2.";
  require 1/a+1/b+1/c lt 1 : "Must be hyperbolic (for now, sorry!)";

  Delta := New(GrpPSL2Tri);
  Delta`TriangleSigma := [];
  Delta`TriangleABC := [a,b,c];
  Delta`TriangleD := 1;

  FDelta<da,db,dc> := FreeGroup(3);
  UDelta<da,db,dc> := quo<FDelta | [da^a, db^b, dc^c, da*db*dc]>;
  Delta`TriangleGroup := UDelta;
  deltas := [Delta | da, db, dc];
  Delta`TriangleGroupMap := map<UDelta -> Delta |
      x :-> &*([Delta!1] cat [deltas[Abs(s)]^Sign(s) : s in Eltseq(x)]), y :-> y`Element>;

  _ := InternalTriangleGroupMapExact(Delta : Simplify := Simplify);

  return Delta;
end intrinsic;

intrinsic TriangleSubgroup(sigma::SeqEnum[GrpPermElt] : Delta := [], Simplify := 1) -> GrpPSL2Tri
  {Creates the triangle subgroup associated to the permutation sigma.
   Creates a new triangle group containing if Delta is not specified.
   "Simplify" records how much to try to simplify the underlying quaternion algebra:
   0 means none, 1 means a bit, 2 means to squeeze every bit.}

  if #sigma eq 2 then
    Append(~sigma, (sigma[2]*sigma[1])^-1);
  else
    assert sigma[3]*sigma[2]*sigma[1] eq Id(Universe(sigma));
  end if;

  require #sigma eq 3 : "sigma must be a permutation triple (or pair)";

  Sd := Universe(sigma);
  require IsTransitive(sub<Sd | sigma>) : "sigma must be a transitive permutation triple";

  Gamma := New(GrpPSL2Tri);

  Gamma`TriangleBool := true;
  Gamma`TriangleSigma := sigma;
  Gamma`TriangleABC := [Order(s) : s in sigma];
  Gamma`TriangleD := Degree(Sd);

  // TO DO: Triangle group, don't initialize everything at start, too time consuming

  if Delta cmpne [] then
    // verify it is a good Delta
    require DefiningABC(Delta) eq Gamma`TriangleABC : "Delta has wrong a,b,c";
    Gamma`TriangleParent := Delta;
  else
    a,b,c := Explode(Gamma`TriangleABC);
    Delta := TriangleGroup(a,b,c : Simplify := Simplify);
    Gamma`TriangleParent := Delta;
  end if;

  Gamma`TrianglePi := Delta`TriangleGroupMap^-1*hom<Delta`TriangleGroup -> Sd | sigma>;
  Gamma`BaseRing := Delta`BaseRing;

  return Gamma;
end intrinsic;

intrinsic ContainingTriangleGroup(Gamma::GrpPSL2Tri) -> GrpPSL2Tri
  {Returns the containing triangle group.}

  if IndexDegree(Gamma) eq 1 then
    return Gamma;
  else
    return Gamma`TriangleParent;
  end if;
end intrinsic;

intrinsic MonodromyGroup(Gamma::GrpPSL2Tri) -> GrpPerm
  {Returns the monodromy group associated to a triangle subgroup.}

  sigma := DefiningPermutation(Gamma);
  if sigma eq [] then
    return SymmetricGroup(1);
  else
    return sub<Universe(sigma) | sigma>;
  end if;
end intrinsic;

intrinsic InternalTriangleIn(x::., Gamma::GrpPSL2Tri) -> BoolElt
  {Returns true if x lies in Gamma by checking cosets.}

  require Type(Parent(x)) eq GrpPSL2Tri : "Must be a triangle group element";

  // verify good triangle group
  Gammap := Parent(x);
  if DefiningABC(Gammap) ne DefiningABC(Gamma) then
    return false, "Triangle groups do not match";
  end if;

  pi := DefiningPermutationRepresentation(Gamma);

  if Parent(x`Element) cmpne ContainingTriangleGroup(Domain(pi))`TriangleGroup then
    print "Warning: coercing into triangle group";
    x`Element := Domain(pi)!Eltseq(x`Element);
  end if;

  // By definition, belongs to Gamma if and only if it fixes 1
  return Eltseq(pi(x))[1] eq 1;
end intrinsic;

intrinsic IsCoercible(Gamma::GrpPSL2Tri, x::.) -> BoolElt, GrpPSL2Elt
  {Internal coercion for triangle subgroups.}

  if IsTriangleGroup(Gamma) then
    Delta := Gamma;
    UDelta := Delta`TriangleGroup;
  else
    Delta := ContainingTriangleGroup(Gamma);
    UDelta := Group(Delta);
  end if;

  case Type(x):
    when RngIntElt:
      if x ne 1 then return false; end if;
      u := New(GrpPSL2Elt);
      u`Element := UDelta!1;
      u`Parent := Gamma;
      return true, u;

    when GrpPSL2Elt:
      // just match up parent triangle groups and try to coerce word
      Gammap := Parent(x);
      if DefiningABC(Gammap) ne DefiningABC(Gamma) then
        return false, "Triangle groups do not match";
      end if;
      x`Element := UDelta!Eltseq(x`Element);
      if IsTriangleGroup(Gamma) or InternalTriangleIn(x, Gamma) then
        x`Parent := Gamma;
        return true, x;
      else
        return false, "g does not belong to Gamma";
      end if;

    when GrpFPElt:
      if Parent(x) ne UDelta then return false; end if;
      g := New(GrpPSL2Elt);
      g`Element := x;
      g`Parent := Delta;
      if IsTriangleGroup(Gamma) or InternalTriangleIn(g, Gamma) then
        g`Parent := Gamma;
        return true, g;
      else
        return false, "g does not belong to Gamma";
      end if;

    when SeqEnum:
      if not IsTriangleGroup(Gamma) then
        return false;
      end if;
      x := UDelta!x;
      g := New(GrpPSL2Elt);
      g`Element := x;
      g`Parent := Gamma;
      return true, g;

  end case;

  return false;
end intrinsic;

intrinsic '.'(Gamma::GrpPSL2Tri, i::RngIntElt) -> GrpPSL2Elt
  {Returns the ith generator of the group Gamma.}

  UGamma, mUGamma := Group(Gamma);
  return mUGamma(UGamma.i);
end intrinsic;

intrinsic 'Id'(Gamma::GrpPSL2Tri) -> GrpPSL2Elt
  {Returns the identity element of Gamma.}

  return Gamma!1;
end intrinsic;




// needed to override Matrix in GrpPSL2

intrinsic Matrix(g::GrpPSL2Elt : Precision := 0) -> GrpMatElt
    {returns an element of a matrix group corresponding to g}
    
    
  if assigned Parent(g)`IsShimuraGroup then
    if Precision eq 0 then
      if not assigned g`MatrixH then
        gmat := (Parent(g)`MatrixRepresentation)(g`Element);
        gmat /:= Sqrt(Determinant(gmat));
        g`MatrixH := gmat;
      end if;
      return g`MatrixH;
    else
      A := Algebra(BaseRing(Parent(g)));
      gmat := FuchsianMatrixRepresentation(A : Precision := Precision)(g`Element);
      gmat /:= Sqrt(Determinant(gmat));
      g`MatrixH := gmat;
      return g`MatrixH;
    end if;
  elif Type(Parent(g)) eq GrpPSL2Tri then
    if Precision ne 0 or not assigned g`MatrixH then
      gmat := InternalTriangleMatrixRepresentation(g : Precision := Precision);
      g`MatrixH := gmat;
    end if;
    return g`MatrixH; 
  else
    return g`Element;
  end if;
end intrinsic;

// other dupls, just to get it to work

intrinsic '^' (A::GrpPSL2Elt,k::RngIntElt) -> GrpPSL2Elt
   {"} // "
   // note, in finding A^k, we must remember that the element
   // defining A, while invertible projectively, might not be
   // invertible in the MatrixGroup of the Parent of A.

   if assigned Parent(A)`IsShimuraGroup and Parent(A)`IsShimuraGroup then
     return Parent(A)!((A`Element)^k);
   elif IsTriangleGroup(Parent(A)) then
     return Parent(A)!((A`Element)^k);   
   end if;

   e := A`Element;
   if k gt 0 then
      s := Eltseq(e^k);
      return Parent(A)!s;
   elif k lt 0 then
      s := Eltseq(Adjoint(e)^(-k));
      return Parent(A)!s;
   else
      return Parent(A)!1;
   end if;
end intrinsic;

intrinsic Quaternion(g::GrpPSL2Elt) -> AlgQuatElt
  {Returns the quaternion corresponding to the Fuchsian group element g.}

  G := Parent(g);
  require assigned G`IsShimuraGroup or IsTriangleGroup(G):
    "Argument must arise from an arithmetic Fuchsian group or triangle subgroup";

  if assigned G`IsShimuraGroup then
    return g`Element;
  else
    Delta := ContainingTriangleGroup(G);
    return (Delta`TriangleGroupMapExact)(g);
  end if;
end intrinsic;

intrinsic 'eq' (A::GrpPSL2Elt,B::GrpPSL2Elt) -> BoolElt
    {Equality of elements of PSL_2(Z)}

    if assigned Parent(A)`IsShimuraGroup and Parent(A)`IsShimuraGroup then
      return A`Element eq B`Element;
    elif Type(Parent(A)) eq GrpPSL2Tri or Type(Parent(B)) eq GrpPSL2Tri then
      require
         Type(Parent(A)) eq GrpPSL2Tri and Type(Parent(B)) eq GrpPSL2Tri :
        "Need both triangle group elements";
      require Parent(A`Element) eq Parent(B`Element) : 
        "Must come from the same triangle group";

      return A`Element eq B`Element;
    end if;

    R1 := BaseRing(Parent(A));
    R2 := BaseRing(Parent(B));
    // WARNING : need to test if elements of A and B can be
    // multiplied together!
    if (Type(R1) ne RngInt or Type(R1) ne FldRat) and
	(Type(R2) ne RngInt or Type(R2) ne FldRat)
	then
	require Type(R1) eq Type(R2): "first and second arguments
	must be defined over compatible rings";
    end if;    
    a_elt := Eltseq(A`Element);
    b_elt := Eltseq(B`Element);
    sA := a_elt[1];
    sB := b_elt[1];
    if sA eq 0 then
	if sB ne 0 then
	    return false;
	else
	    sA := a_elt[2];
	    sB := b_elt[2];
	end if;
    elif sB eq 0 then
	return false;	
    end if;
    if Type(R1) eq FldNum and Type(R2) eq FldNum then
	if R1 ne R2 then
	    K := NumberField(R1,R2);
	    return
	    &and[K!(a_elt[i]/sA) eq K!(b_elt[i]/sB) : i in [1..4]]; 
	end if;
    end if;    
    return &and[a_elt[i]/sA eq b_elt[i]/sB : i in [1..4]]; 
end intrinsic;

intrinsic '*' (A::GrpPSL2Elt,z::SpcHypElt) -> SpcHypElt
   {"} // "
   // Action on elements of upper half plane union cusps:
   if assigned Parent(A)`IsShimuraGroup or Type(Parent(A)) eq GrpPSL2Tri then
     a,b,c,d := Explode(Eltseq(Matrix(A)));
     return Parent(z)!((a*z`complex_value+b)/(c*z`complex_value+d));
   end if;

   a,b,c,d := Explode(Eltseq(A`Element));
   if IsCusp(z) and Type(ExactValue(z)) eq SetCspElt then
      //	require Type(a) in {FldRatElt, RngIntElt}:
      //	"Argument 1 must be defined over the rationals " *
      //	"or integers when argument 2 is a cusp.";
      //      warning : possibly this may not return cusps when
      //      applied to cusps.
      u,v := Explode(Eltseq(z`exact_value));
      if c*u+d*v eq 0 then
	 return Parent(z)!Cusps()![1,0];
      else
	 frac := (a*u + b*v)/(c*u+d*v);
	 return Parent(z)!frac; //frac;	   
      end if;
   // elif z`is_exact and  (Type(a) in [FldRatElt,RngIntElt]) then
   elif z`is_exact then
      // In the exact case, assume either that a,b,c, and d are rationals
      // or integers, or that they are elements of a
      // fixed real quadratic field K, and ze is in 
      // some relative (quadratic) extension of K.       	
      ze := z`exact_value;
      if (c*ze+d) eq 0 then
	 return Parent(z)!Cusps()![1,0];
      else
	 frac := (a*ze+b)/(c*ze+d);
	 return Parent(z)!frac;
      end if;
   else
      // in the none exact case, assume that a,b,c, and d are
      // either elements
      // of the integers or rationals, OR are elements
      // of a real quadratic field.
      // if not, use the following hack:
      if Type(Parent(a)) eq FldRe then
        a,b,c,d := Explode(Eltseq(A`Element));
      elif not (Parent(a) cmpeq Integers()
	 or Parent(a) cmpeq Rationals()) then       
	 a,b,c,d := Explode([Conjugates(x)[1] : x in (Eltseq(A`Element))]);
      end if;
      if (c*z`complex_value+d) eq 0 then
	 return Parent(z)!Infinity();
      else	  
	 return Parent(z)!((a*z`complex_value+b)/
	 (c*z`complex_value+d));
      end if;
   end if;
end intrinsic;

