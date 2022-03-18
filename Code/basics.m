intrinsic Genus(Gamma::GrpPSL2Tri) -> RngIntElt
  {Returns the genus of the quotient of the upper half-plane by Gamma.}

  if IsTriangleGroup(Gamma) then
    return 0;
  end if;

  // Riemann-Hurwitz formula
  sigma := DefiningPermutation(Gamma);
  /*
    d := IndexDegree(Gamma);
    g2 := -2*d + &+[&+[ e[2]*(e[1]-1) : e in CycleStructure(sigma[i])] : i in [1..3]];
    g := (g2+2)/2;
    g := Integers()!g;
  */
  return Genus(sigma);
end intrinsic;

intrinsic Genus(sigma::SeqEnum[GrpPermElt]) -> RngIntElt
  {Returns the genus of the quotient of the upper half-plane by the triangle subgroup associated to sigma.}
  d := Degree(Parent(sigma[1]));
  // Riemann-Hurwitz formula
  g2 := -2*d + &+[&+[ e[2]*(e[1]-1) : e in CycleStructure(sigma[i])] : i in [1..3]];
  assert g2 mod 2 eq 0;
  g := (g2+2) div 2;
  return g;
end intrinsic;

intrinsic Signature(Gamma::GrpPSL2Tri) -> SeqEnum
  {Returns the signature of the quotient of the upper half-plane by Gamma.}

  abc := DefiningABC(Gamma);

  if IsTriangleGroup(Gamma) then
    ellinvs := abc;
  else
		sigma := DefiningPermutation(Gamma);
		ellinvs := [];
		for i := 1 to 3 do
			s := abc[i];
			for e in CycleStructure(sigma[i]) do
				for j := 1 to e[2] do
					Append(~ellinvs, s div e[1]);
				end for;
			end for;
		end for;
		ellinvs := [e : e in ellinvs | e ne 1];
  end if;

	Sort(~ellinvs);

  return <Genus(Gamma), ellinvs>;
end intrinsic;

intrinsic AutomorphismGroup(Gamma::GrpPSL2Tri) -> GrpPerm
  {For Gamma a triangle subgroup, returns the automorphism group of the
   associated Belyi map.}

  sigma := DefiningPermutation(Gamma);
  Sd := Universe(sigma);
  return Centralizer(Sd, sub<Sd | sigma>);
end intrinsic;

intrinsic QuaternionAlgebra(Gamma::GrpPSL2Tri) -> AlgQuat
  {For Gamma a triangle subgroup, returns the quaternion algebra asssocaited
  to Gamma.}

  return Gamma`BaseRing;
end intrinsic;

/*
----------------------------------------------------------------------------
----------------------------------------------------------------------------
SkDimension
Input:
  Gamma: Triangle subgroup
  k: Weight of space of modular forms Sk
Output:
  return: The dimension of Sk, the space of modular forms of weight k
----------------------------------------------------------------------------
*/

intrinsic SkDimension(Gamma::GrpPSL2Tri, k::RngIntElt) -> RngIntElt
  {Returns the dimension of the vector space Sk of modular forms of weight k for Gamma.}

  require k mod 2 eq 0 : "k must be even";

  g := Genus(Gamma);
  cycles := Signature(Gamma)[2];

  if k lt 0 then
    dim := 0;
  elif k eq 0 then
    dim := 1;
  elif k eq 2 then
    dim := g;
  elif k gt 2 then
    dim := (k-1)*(g-1) + &+[Floor((k*(e-1))/(2*e)) : e in cycles];
  end if;

  return dim;
end intrinsic;
