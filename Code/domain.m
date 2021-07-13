intrinsic FundamentalDomain(Gamma::GrpPSL2Tri) -> SeqEnum
  {Returns a fundamental domain for Gamma in the upper half-plane.}

  H := UpperHalfPlaneWithCusps();
  return FundamentalDomain(Gamma,H);
end intrinsic;
   
intrinsic FundamentalDomain(Gamma::GrpPSL2Tri, D::SpcHyd) -> SeqEnum
  {Returns a fundamental domain for Gamma in the unit disc D.}

  FD := FundamentalDomain(Gamma);
  return [PlaneToDisc(D, x) : x in FD];
end intrinsic;




