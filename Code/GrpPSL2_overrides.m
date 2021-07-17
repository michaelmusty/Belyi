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

intrinsic Matrix(g::GrpPSL2Elt, D::SpcHyd) -> AlgMatElt
  {Returns the matrix representation of g acting on the unit disc D.}

  if assigned g`MatrixD and g`MatrixDCenter eq Center(D) and 
      Precision(BaseRing(Parent(g`MatrixD))) eq D`prec then
    return g`MatrixD;
  end if;
  RR := RealField(Parent(ComplexValue(Center(D))));
  M := Matrix(g : Precision := Precision(RR));
  ctr := ComplexValue(Center(D) : Precision:=Precision(RR), CheckInfinite:=false);
  rot := Exp(Parent(ctr).1*Rotation(D));
  Z0 := MatrixRing(ComplexField(RR), 2)![rot,-rot*ctr,1,-ComplexConjugate(ctr)];
  g`MatrixD := Z0*M*Z0^(-1);
  g`MatrixDCenter := Center(D);
  return g`MatrixD;
end intrinsic;

// other dupls, just to get it to work

intrinsic '^' (A::GrpPSL2Elt,k::RngIntElt) -> GrpPSL2Elt
   {"} // "
   // note, in finding A^k, we must remember that the element
   // defining A, while invertible projectively, might not be
   // invertible in the MatrixGroup of the Parent of A.

   if assigned Parent(A)`IsShimuraGroup and Parent(A)`IsShimuraGroup then
     return Parent(A)!((A`Element)^k);
   elif Type(Parent(A)) eq GrpPSL2Tri then
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
  require assigned G`IsShimuraGroup or Type(G) eq GrpPSL2Tri:
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
     zcc := z`complex_value;
     prec := Precision(Parent(zcc));
     a,b,c,d := Explode(Eltseq(Matrix(A : Precision := prec)));
     return Parent(z)!((a*zcc+b)/(c*zcc+d));
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



function init_psl2_elt(G,A)
    /* The basic internal creation function. */ 
    X := New(GrpPSL2Elt); 
    X`Parent := G;
    coeffs := [ x : x in Eltseq(A) ];
    // some normalization of coefficients:
    if Type(G) eq FldRat then
	if G`BaseRing eq Rationals() then
	    // multiply through by lcm of denominaors,
	    // then divide by gcd of matrix entries
	    // to get a matrix with coprime integer entries
	    // if the BaseRing is the integers, then we should
	    // already have this propetry.
	    denoms := [Denominator(a) : a in coeffs];
	    numers := [Numerator(a) : a in coeffs];
	    gcd := Gcd(numers);
	    lcm := Lcm(denoms);
	    coeffs := [ Integers()!(x*lcm/gcd) : x in coeffs];	
	    if (coeffs[1] lt 0) or
		(coeffs[1] eq 0 and coeffs[2] lt 0) then
		coeffs := [-x : x in coeffs];	    
	    end if;	    
	end if;
    end if;
    if Type(G) eq RngInt then
	if G`BaseRing eq Integers() or G`BaseRing eq Rationals() then
	    if (coeffs[1] lt 0) or
		(coeffs[1] eq 0 and coeffs[2] lt 0) then
		coeffs := [-x : x in coeffs];	    
	    end if;	    
	end if;
    end if;	
    X`Element := A;
    return X;
end function; 

intrinsic '*' (A::GrpPSL2Elt,B::GrpPSL2Elt) -> GrpPSL2Elt
    {"} // "
    GA := Parent(A);
    GB := Parent(B);
    if Type(Parent(A)) eq GrpPSL2Tri or Type(Parent(B)) eq GrpPSL2Tri then
      require
         Type(Parent(A)) eq GrpPSL2Tri and Type(Parent(B)) eq GrpPSL2Tri :
           "Invalid triangle group multiplication";
      require Parent(A`Element) eq Parent(B`Element) : 
           "Can only multiply in the same containing triangle group";
      AB := A`Element*B`Element;
      if GA eq GB then
        parentAB := GA;
      else
        // give up and just return something in the underlying triangle group.
        parentAB := ContainingTriangleGroup(GA);
      end if;
      return init_psl2_elt(parentAB, AB);
    elif GA`BaseRing cmpeq GB`BaseRing then
      if assigned GA`IsShimuraGroup and assigned GB`IsShimuraGroup then
        return init_psl2_elt(GA, A`Element*B`Element);
      end if;
       if GA eq GB then
 	    return init_psl2_elt(GA, A`Element*B`Element);
	else
	    P := PSL2(GA`BaseRing);
	    return init_psl2_elt(P, A`Element*B`Element);
	end if;
    end if;		
    error if true, "Incompatible base rings.";
end intrinsic;