intrinsic FundamentalDomain(Gamma::GrpPSL2Tri : Precision := 0) -> SeqEnum
  {Returns a fundamental domain for Gamma in the upper half-plane.}

  H := UpperHalfPlane();
  return FundamentalDomain(Gamma,H : Precision := Precision);
end intrinsic;
   
intrinsic FundamentalDomain(Gamma::GrpPSL2Tri, D::SpcHyd : Precision := 0) -> SeqEnum
  {Returns a fundamental domain for Gamma in the unit disc D.}

  FDH := FundamentalDomain(Gamma : Precision := Precision);
  FD := [PlaneToDisc(D, x) : x in FDH];
  Gamma`TriangleFD := FDH;
  return FD;
end intrinsic;
