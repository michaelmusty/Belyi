intrinsic VarSeq(var::MonStgElt, lower::RngIntElt, upper::RngIntElt) -> SeqEnum[MonStgElt]
  {returns SeqEnum ["varlower", "varlower+1", ..., "varupper-1", "varupper"].}
  assert upper ge lower;
  var_seq := [];
  for i := lower to upper do
    Append(~var_seq, Sprintf("%o%o", var, i));
  end for;
  return var_seq;
end intrinsic;

intrinsic ExtractRoot(Y::Crv, f::FldFunFracSchElt, m::RngIntElt, genus::RngIntElt) -> Crv
  {Given a curve Y, and f in KY the function field of Y, return a new curve X with function field KX where KX = KY(mthroot(f)).}
  // assertions
    if not IsAffine(Y) then
      Y := AffinePatch(Y, 1);
    end if;
    KY := FunctionField(Y);
    assert Parent(f) eq KY;
  // ambient, ideal, polynomial ring of Y
    IY := Ideal(Y);
    PY := Generic(IY);
    AAY := Ambient(Y);
  // polynomial ring and ideal upstairs
    IYext, mp := VariableExtension(IY, 1, false); // mp: PY -> PX
    PX := Codomain(mp);
    assert PX eq Generic(IYext);
    AssignNames(~PX, VarSeq("x", 1, Rank(PX)));
  // map numerator and denominator of f into PX
    numer := mp(Numerator(f, Y));
    denom := mp(Denominator(f, Y));
  // basis of new ideal
    basis := Basis(IYext);
    new_equation := denom*PX.Rank(PX)^m-numer;
    Append(~basis, new_equation);
    IX := ideal< PX | basis >;
    S := Saturation(IX, denom); // saturate at denominator
    assert IsPrime(S);
  // new ambient
    AAX := AffineSpace(PX);
  // make curve and test if the genus is correct
    X := Curve(AAX, S);
    assert Genus(X) eq genus;
    return X;
end intrinsic;
