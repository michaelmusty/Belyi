// previous version of galoisorbits.m renamed recognition.m 2018/02/26
// 7T6-[7,7,3]-7-7-331-g2.m
// 7T7-[4,12,12]-421-43-43-g1.m

intrinsic Polredbest(f::RngUPolElt) -> RngUPolElt
  { A smallest generating polynomial of the number field, using pari. }
  cmd := Sprintf(
   "{print(Vecrev(Vec(polredbest(Pol(Vecrev(%o))))))}",
   Coefficients(f));
  s := Pipe("gp -q", cmd);
  ss := [ StringToInteger(x)
  : x in Split(s, ", []\n") | x ne "" ];
  return Parent(f) ! ss;
end intrinsic;

intrinsic Polredabs(f::RngUPolElt) -> RngUPolElt
  { A smallest generating polynomial of the number field, using pari. }
  cmd := Sprintf(
   "{print(Vecrev(Vec(polredabs(Pol(Vecrev(%o))))))}",
   Coefficients(f));
  s := Pipe("gp -q", cmd);
  ss := [ StringToInteger(x)
  : x in Split(s, ", []\n") | x ne "" ];
  return Parent(f) ! ss;
end intrinsic;

intrinsic Polredabsbest(f::RngUPolElt) -> RngUPolElt
  {best is fast, abs is unique...I think...}
  return Polredabs(Polredbest(f));
end intrinsic;

intrinsic Polredabs(K::FldNum) -> Any
  {}
  if Degree(K) le 1 then
    assert K eq RationalsAsNumberField();
    return K;
  else
    vprintf Shimura : "\nTrying to optimize using Polredabs\n";
    Kop := NumberField(Polredabsbest(DefiningPolynomial(K)));
    vprintf Shimura : "Optimized. Trying to obtain an isomorphism.\n";
    bl, iotaop := IsIsomorphic(K, Kop);
    vprintf Shimura : "Done.\n";
    assert bl;
    return Kop, iotaop;
  end if;
end intrinsic;

intrinsic Eval(alpha::FldNumElt, v::PlcNumElt, is_conjugated::BoolElt) -> FldComElt
  {}
  z := Evaluate(alpha, v);
  if is_conjugated then
    return ComplexConjugate(z);
  else
    return z;
  end if;
end intrinsic;

intrinsic Eval(l::List) -> FldComElt
  {}
  return Eval(l[1].1, l[2], l[3]);
end intrinsic;

intrinsic MachineZero(z::FldReElt) -> BoolElt
  {}
  prec := Precision(Parent(z));
  if AbsoluteValue(z) le 10^(-prec/2) then
    return true;
  else
    return false;
  end if;
end intrinsic;

intrinsic MachineZero(z::FldComElt) -> BoolElt
  {}
  prec := Precision(Parent(z));
  if AbsoluteValue(z) le 10^(-prec/2) then
    return true;
  else
    return false;
  end if;
end intrinsic;

intrinsic Polredabs(mp::Map, K::FldNum, vK::PlcNumElt, is_conjugated::BoolElt) -> Any
  {returns L, vL, and a boolean where L is Polredabs(K) and vL is pullback of vK under the isomorphism mp : L -> K.}
  if Degree(K) eq 1 then // we don't polredabsify QQ
    return K, vK, is_conjugated;
  end if;
  /*
  // after we do some sanity checking uncomment this
  if DefiningPolynomial(K) eq Polredabs(DefiningPolynomial(K)) then
    return l;
  end if;
  */
  assert ISA(Type(K), FldNum) and ISA(Type(vK), PlcNumElt) and ISA(Type(is_conjugated), BoolElt);
  L := Domain(mp); // mp : L -> K
  assert DefiningPolynomial(L) eq DefiningPolynomial(Polredabs(L));
  assert DefiningPolynomial(L) eq DefiningPolynomial(Polredabs(K));
  assert K eq Codomain(mp);
  vprintf Shimura : "Starting field: \n%o\n", K;
  if IsReal(vK) then
    vprintf Shimura : "Real place : %o\n", vK;
  else
    vprintf Shimura : "Complex place : %o, %o\n", vK, is_conjugated;
  end if;
  vprintf Shimura : "Isomorphism : ";
  if mp(L.1) eq K.1 then
    vprintf Shimura : "identity : ";
  end if;
  vprintf Shimura : "%o -> %o\n", L.1, mp(L.1);
  vprintf Shimura : "\n";
  places_K := InfinitePlaces(K);
  places_L := InfinitePlaces(L);
  assert #places_K eq #places_L;
  assert vK in places_K;
  for vL in places_L do
    if Extends(vL, vK) then
      if IsReal(vL) then
        assert IsReal(vK);
        test_value := Evaluate(L.1, vL) - Evaluate(mp(L.1), vL);
        assert MachineZero(test_value);
        return L, vL, false;
      else // vL is a complex place
        test_true := Eval(L.1, vL, true) - Eval(mp(L.1), vK, is_conjugated);
        test_false := Eval(L.1, vL, false) - Eval(mp(L.1), vK, is_conjugated);
        if MachineZero(test_true) then
          return L, vL, true;
        elif MachineZero(test_false) then
          return L, vL, false;
        else
          error "failed to pullback complex place!";
        end if;
      end if;
    end if;
  end for;
end intrinsic;

intrinsic Polredabs(l::List) -> List
  {overloaded for [K,vK,conj] or [K,vK,conj,zCC]}
  assert #l in [3, 4];
  K := l[1];
  vK := l[2];
  is_conjugated_K := l[3];
  assert ISA(Type(K), FldNum) and ISA(Type(vK), PlcNumElt) and ISA(Type(is_conjugated_K), BoolElt);
  if #l eq 4 then
    assert ISA(Type(l[4]), FldComElt);
  end if;
  L := Polredabs(K);
  is_iso, mp := IsIsomorphic(L, K);
  assert is_iso;
  L, vL, is_conjugated_L := Polredabs(mp, K, vK, is_conjugated_K);
  if #l eq 3 then
    return [* L, vL, is_conjugated_L *];
  else
    return [* L, vL, is_conjugated_L, l[4] *];
  end if;
end intrinsic;

intrinsic Polredabs(s::BelyiDB) -> BelyiDB
  {Polredabs fields, curves, and maps of s.}
  // assert BaseFieldDataSanityCheck(s);
  ppass := s`BelyiDBPointedPassport;
  lists := s`BelyiDBBaseFieldData;
  curves := s`BelyiDBBelyiCurves;
  maps := s`BelyiDBBelyiMaps;
  assert #SequenceToSet([#lists, #curves, #maps, #ppass]) eq 1;
  // base field data: TODO fix isomorphisms
  for l in lists do
    assert IsAbsoluteField(l[1]);
  end for;
  s`BelyiDBBaseFieldData := [* Polredabs(l) : l in lists *];
  // curves
  // maps
end intrinsic;

/* TODO
intrinsic BaseFieldDataSanityCheck(s::BelyiDB) -> BoolElt
  {assert that the list of quadruples [K,place,is_conj,zCC] includes all possible real places and pairs of complex places.}
  lists := s`BelyiDBBaseFieldData;
end intrinsic;
*/

intrinsic IsPolredabsMatch(s::BelyiDB) -> BoolElt
  {check that base fields of the passport match polredabs.}
  ppass := s`BelyiDBPointedPassport;
  assert #SequenceToSet([#s`BelyiDBBaseFieldData, #s`BelyiDBBelyiCurves, #s`BelyiDBBelyiMaps, #s`BelyiDBPointedPassport]) eq 1;
  curves := s`BelyiDBBelyiCurves;
  maps := s`BelyiDBBelyiMaps;
  fields := [];
  for i := 1 to #ppass do
    Append(~fields, AbsoluteField(s`BelyiDBBaseFieldData[i][1]));
    assert #GeneratorsSequence(fields[i]) eq 1;
  end for;
  bools := [];
  for i := 1 to #fields do
    F := fields[i];
    X := curves[i];
    F_X := BaseField(X);
    phi := maps[i];
    assert Parent(phi) eq FunctionField(X);
    F_phi := BaseField(Curve(Parent(phi)));
    if Degree(F) gt 1 then
      field_bool := DefiningPolynomial(F) eq Polredabs(DefiningPolynomial(F));
      curve_bool := DefiningPolynomial(F_X) eq Polredabs(DefiningPolynomial(F_X));
      map_bool := DefiningPolynomial(F_phi) eq Polredabs(DefiningPolynomial(F_phi));
      bool := field_bool and curve_bool and map_bool;
      Append(~bools, bool);
    end if;
  end for;
  if #SequenceToSet(bools) eq 1 then
    return true;
  else
    return false;
  end if;
end intrinsic;

intrinsic CompareUpToBaseFieldIsomorphism(f1::FldFunFracSchElt, f2::FldFunFracSchElt) -> BoolElt
  {True if f1 and f2 have isomorphic base fields and have the same coefficients after applying this isomorphism.}
  K1 := BaseField(Curve(Parent(f1)));
  K2 := BaseField(Curve(Parent(f2)));
  is_iso, mp := IsIsomorphic(K1, K2);
  if is_iso then
    printf "%o\n",mp;
    num_1 := Coefficients(Numerator(f1));
    num_2 := Coefficients(Numerator(f2));
    den_1 := Coefficients(Denominator(f1));
    den_2 := Coefficients(Denominator(f2));
    printf "alpha1     = %o\n", num_1[1];
    printf "mp(alpha1) = %o\n", mp(num_1[1]);
    printf "alpha2     = %o\n", num_2[1];
    if mp(num_1) eq num_2 and mp(den_1) eq den_2 then
      return true;
    else
      return false;
    end if;
  else
    return false;
  end if;
end intrinsic;

// [K,place,conj] -> [K',place',conj'] polredabsified

/*
intrinsic BelyiDBGaloisOrbitsComputer(s::BelyiDB) -> BelyiDB
  {Given a BelyiDB object with BelyiMaps computed return the BelyiDB object with passport split into Galois orbits.}
  assert #SequenceToSet([#s`BelyiDBBaseFieldData, #s`BelyiDBBelyiCurves, #s`BelyiDBBelyiMaps, #s`BelyiDBPointedPassport]) eq 1; // assert all lists have the right size
  ppass := s`BelyiDBPointedPassport;
  fields := [];
  minpolys := [];
  maps := [* *];
  for i := 1 to #ppass do
    Append(~fields, AbsoluteField(s`BelyiDBBaseFieldData[i][1]));
    assert #GeneratorsSequence(fields[i]) eq 1;
    Append(~minpolys, MinimalPolynomial(fields[i].1));
    Append(~maps, s`BelyiDBBelyiMaps[i]);
  end for;
  minpolys_notQQ := [];
  fields_notQQ := [];
  ppass_notQQ := [];
  maps_notQQ := [* *];
  gal_fields := [];
  gal_minpolys := [];
  gal_ppass := [];
  gal_maps := [* *];
  for i := 1 to #ppass do
    if Degree(fields[i]) eq 1 then // all QQ in single orbit
      Append(~gal_fields, [fields[i]]);
      Append(~gal_ppass, [ppass[i]]);
      Append(~gal_minpolys, [minpolys[i]]);
      Append(~gal_maps, [* maps[i] *]);
    else // all notQQ in new list to check iso
      Append(~fields_notQQ, fields[i]);
      Append(~ppass_notQQ, ppass[i]);
      Append(~minpolys_notQQ, minpolys[i]);
      Append(~maps_notQQ, maps[i]);
    end if;
  end for;
  if #fields_notQQ gt 0 then
    Append(~gal_fields, [fields_notQQ[1]]);
    Append(~gal_minpolys, [minpolys_notQQ[1]]);
    Append(~gal_ppass, [ppass_notQQ[1]]);
    Append(~gal_maps, [* maps_notQQ[1] *]);
    for i := 2 to #fields_notQQ do // i loops over all not QQ fields
      new_orbit := true; // new orbit by default
      for j := 1 to #gal_fields do // j loops over all galois orbits so far
        // TODO IsIsomorphic causes SEG FAULT for 7T6-[4,4,4]-421-421-421-g0
        // 7T6-[4,4,4]-421-421-421-g0
        // if IsIsomorphic(fields_notQQ[i], gal_fields[j][1]) and minpolys_notQQ[i] eq gal_minpolys[j][1] then
        // if IsIsomorphic(fields_notQQ[i], gal_fields[j][1]) then // hacky? no, wrong
        // if minpolys_notQQ[i] eq gal_minpolys[j][1] and BelyiDBCompareBelyiMaps(maps_notQQ[i], gal_maps[j][1]) then
        print IsIsomorphic(fields_notQQ[i], gal_fields[j][1]);
        print BelyiDBCompareBelyiMaps(maps_notQQ[i], gal_maps[j][1]);
        if IsIsomorphic(fields_notQQ[i], gal_fields[j][1]) and BelyiDBCompareBelyiMaps(maps_notQQ[i], gal_maps[j][1]) then
          Append(~gal_fields[j], fields_notQQ[i]);
          Append(~gal_ppass[j], ppass_notQQ[i]);
          Append(~gal_minpolys[j], minpolys_notQQ[i]);
          Append(~gal_maps[j], maps_notQQ[i]);
          new_orbit := false;
        end if;
      end for;
      if new_orbit then
        Append(~gal_fields, [fields_notQQ[i]]);
        Append(~gal_ppass, [ppass_notQQ[i]]);
        Append(~gal_minpolys, [minpolys_notQQ[i]]);
        Append(~gal_maps, [* maps_notQQ[i] *]);
      end if;
    end for;
  end if;
  s`BelyiDBGaloisOrbits := gal_ppass;
  return s;
end intrinsic;
*/

intrinsic BelyiConstant(d_bound::RngIntElt, k::RngIntElt) -> FldRatElt
  {}
  RR := RealField();
  if d_bound le 4 then
    return RR!1;
  end if;
  // d=1
  num_passes := 1;
  num_orbits := 1;
  // d>1
  for d := 2 to d_bound do
    t0 := Cputime();
    all := [BelyiDBRead(f) : f in BelyiDBFilenames(d)];
    size_k := [];
    for s in all do
      if #s`BelyiDBPointedPassport le k then
        Append(~size_k, s);
      end if;
    end for;
    num_passes +:= #size_k;
    num_orbits_d_k := 0;
    for s in size_k do
      if assigned s`BelyiDBBelyiCurves then
        if assigned s`BelyiDBGaloisOrbits then
          num_orbits_d_k +:= #s`BelyiDBGaloisOrbits;
        else
          error Sprintf("%o has size le %o with Belyi maps computed but Galois orbits not computed.\n", s`BelyiDBName, k);
        end if;
      else
        error Sprintf("%o has size le %o but Belyi maps not computed.\n", s`BelyiDBName, k);
      end if;
    end for;
    num_orbits +:= num_orbits_d_k;
    t1 := Cputime();
    vprintf Shimura : "d=%o: %o seconds.\n", d, t1-t0;
  end for;
  vprintf Shimura : "#passports: %o\n", num_passes;
  vprintf Shimura : "#orbits: %o\n", num_orbits;
  return RR!(num_passes/num_orbits);
end intrinsic;

intrinsic GaloisOrbitsSanityCheck(s::BelyiDB) -> BoolElt
  {}
  if assigned s`BelyiDBGaloisOrbits then
    fields := [s`BelyiDBBaseFieldData[i][1] : i in [1..#s`BelyiDBBaseFieldData]];
    distinct := [];
    for i := 1 to #fields do
      K := fields[i];
      if Degree(K) eq 1 then
        Append(~distinct, K);
      else
        is_new := true;
        for F in distinct do
          if IsIsomorphic(K,F) then
            is_new := false;
          end if;
        end for;
        if is_new then
          Append(~distinct, K);
        end if;
      end if;
    end for;
    if #distinct eq #s`BelyiDBGaloisOrbits then
      return true;
    else
      return false;
    end if;
  else
    error "Galois orbits not computed.\n";
  end if;
end intrinsic;

