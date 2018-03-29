// user convenience

intrinsic BelyiDBFields(d::RngIntElt) -> List
  {for internal use only}
  l_d := [* *];
  filenames_d := BelyiDBFilenames(d);
  for i := 1 to #filenames_d do
    s := BelyiDBRead(filenames_d[i]);
    if assigned s`BelyiDBBaseFieldData then
      name_s := s`BelyiDBName;
      fields_s := s`BelyiDBBaseFieldData;
      l_s := [* *];
      for j := 1 to #fields_s do
        Append(~l_s, fields_s[j][1]);
      end for;
      Append(~l_d, [* name_s, l_s *]);
    end if;
  end for;
  return l_d;
end intrinsic;

intrinsic BelyiDBGetDegreeGroupGenus(filename::MonStgElt) -> SeqEnum[RngIntElt]
  {returns integers [d,group,genus] for a filename.}
  // directory stuff
    dir := GetCurrentDirectory();
    parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
    if parentdir eq "BelyiDB\n" then
      dbdirectory := dir;
    else
      error "make sure your working directory is /BelyiDB";
    end if;
  // degree
    num_chars := 0;
    for i in {1..#filename} do
      if filename[i] eq "T" then
        num_chars := i-1;
      end if;
    end for;
    assert num_chars ne 0;
    d_str := "";
    for i in {1..num_chars} do
      d_str *:= filename[i];
    end for;
    d := StringToInteger(d_str);
  // group
  dash_splits := Split(filename, "-");
  group_str := dash_splits[1];
  group_str := Split(group_str, "T")[2];
  group := StringToInteger(group_str);
  // genus
  genus_str := dash_splits[#dash_splits];
  genus_str := Split(genus_str, ".")[1];
  genus_str := Split(genus_str, "g")[2];
  genus := StringToInteger(genus_str);
  // return
  return [d, group, genus];
end intrinsic;

intrinsic BelyiDBGetFilenames(d::RngIntElt, group::RngIntElt, genus::RngIntElt : ignore_group := false) -> Any
  {returns all BelyiDBobject filenames with given degree, group, and genus.}
  // directory stuff
    dir := GetCurrentDirectory();
    parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
    if parentdir eq "BelyiDB\n" then
      dbdirectory := dir;
    else
      error "make sure your working directory is /BelyiDB";
    end if;
  // get filenames
  f := BelyiDBFilenames(d);
  names := [];
  if ignore_group then
    for i := 1 to #f do
      l := BelyiDBGetDegreeGroupGenus(f[i]);
      d_test := l[1];
      genus_test := l[3];
      if d_test eq d and genus_test eq genus then
        Append(~names, f[i]);
      end if;
    end for;
  else
    for i := 1 to #f do
      if BelyiDBGetDegreeGroupGenus(f[i]) eq [d, group, genus] then
        Append(~names, f[i]);
      end if;
    end for;
  end if;
  // return
  return names;
end intrinsic;

intrinsic BelyiDBGetPassports(d::RngIntElt, group::RngIntElt, genus::RngIntElt) -> Any
  {returns all passports with given degree, group, and genus.}
  // directory stuff
    dir := GetCurrentDirectory();
    parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
    if parentdir eq "BelyiDB\n" then
      dbdirectory := dir;
    else
      error "make sure your working directory is /BelyiDB";
    end if;
  // get objects
  objs := BelyiDBGet(d, group, genus);
  // make passports
  passports := [obj`BelyiDBPointedPassport : obj in objs];
  // return
  return passports;
end intrinsic;

intrinsic BelyiDBGet(d::RngIntElt, group::RngIntElt, genus::RngIntElt : hyperbolic := false, nonhyperbolic := false, ignore_group := false) -> Any
  {returns all BelyiDBobjects with given degree, group, and genus, setting hyperbolic (resp. nonhyperbolic) returns only those that are hyperbolic (resp. nonhyperbolic), returns both hyperbolic and nonhyperbolic by default.}
  assert not (hyperbolic and nonhyperbolic);
  // directory stuff
    dir := GetCurrentDirectory();
    parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
    if parentdir eq "BelyiDB\n" then
      dbdirectory := dir;
    else
      error "make sure your working directory is /BelyiDB";
    end if;
  // get filenames and read in
  names := BelyiDBGetFilenames(d, group, genus : ignore_group := ignore_group);
  objs := [BelyiDBRead(name) : name in names];
  // hyperbolic only
  hyp := [];
  if hyperbolic then
    for s in objs do
      if s`BelyiDBType eq "Hyperbolic" then
        Append(~hyp, s);
      end if;
    end for;
    objs := hyp;
  end if;
  // nonhyperbolic only
  nonhyp:= [];
  if nonhyperbolic then
    for s in objs do
      if not s`BelyiDBType eq "Hyperbolic" then
        Append(~nonhyp, s);
      end if;
    end for;
    objs := nonhyp;
  end if;
  // return
  return objs;
end intrinsic;

intrinsic BelyiDBGet(d::RngIntElt, genus::RngIntElt : hyperbolic := false, nonhyperbolic := false) -> Any
  {overloaded to ignore group.}
  return BelyiDBGet(d, 1, genus : hyperbolic := hyperbolic, nonhyperbolic := nonhyperbolic, ignore_group := true);
end intrinsic;

intrinsic MakeBaseFieldData(sigma::SeqEnum[GrpPermElt], X::Crv, phi::FldFunFracSchElt : conj := false, plc_index := 1, prec := 20, field_index := 1) -> Any
  {returns [* K, Kv, conj, zCC *] with zCC = 0 for use with BelyiDBWrite.}
  assert Parent(phi) eq FunctionField(X);
  assert BelyiMapSanityCheck(sigma, X, phi);
  K := BaseField(X);
  if not ISA(Type(K), FldNum) then
    assert field_index eq 1;
    assert K eq Rationals();
    K<nu1> := RationalsAsNumberField();
  else
    AssignNames(~K, [Sprintf("nu%o", field_index)]);
  end if;
  zCC := ComplexField(prec)!0;
  conj := conj;
  Kv := InfinitePlaces(K)[plc_index];
  return [* K, Kv, conj, zCC *];
end intrinsic;

intrinsic BelyiDBAdhoc(s::BelyiDB) -> Any
  {internal use for size 1 nonhyperbolic.}
  assert s`BelyiDBType ne "Hyperbolic";
  pass := s`BelyiDBPointedPassport;
  assert #pass eq 1;
  sigma := pass[1];
  if s`BelyiDBType eq "Spherical" then
    X, phi := SphericalBelyiMap(sigma);
  else
    X, phi := EuclideanBelyiMap(sigma);
  end if;
  for tau in Sym(3) do
    phi_tau := S3Action(tau, phi);
    if BelyiMapSanityCheck(sigma, X, phi_tau) then
      phi := phi_tau;
    end if;
  end for;
  assert BelyiMapSanityCheck(sigma, X, phi);
  bfd := MakeBaseFieldData(sigma, X, phi);
  s`BelyiDBBaseFieldData := [* bfd *];
  s`BelyiDBBelyiCurves := [* X *];
  s`BelyiDBBelyiMaps := [* phi *];
  BelyiDBWrite(s);
  t := BelyiDBRead(s`BelyiDBFilename);
  assert BelyiMapSanityCheck(t);
  return t;
end intrinsic;

// base code

intrinsic BelyiDBRead(filename::MonStgElt) -> Any
  {Read in the BelyiDB in filename. Assumes current directory is /BelyiDB.}
  // directory stuff
    dir := GetCurrentDirectory();
    parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
    if parentdir eq "BelyiDB\n" then
      dbdirectory := dir;
    else
      error "make sure your working directory is /BelyiDB";
    end if;
  num_chars := 0;
  for i in {1..#filename} do
    if filename[i] eq "T" then
      num_chars := i-1;
    end if;
  end for;
  assert num_chars ne 0;
  d_str := "";
  for i in {1..num_chars} do
    d_str *:= filename[i];
  end for;
  d := StringToInteger(d_str);
  file := dbdirectory cat Sprintf("/%o/%o", d, filename);
  str := Read(file);
  // eval
  s := eval str;
  assert Type(s) eq BelyiDB;
  return s;
end intrinsic;

intrinsic BelyiDBStringToCode(str::MonStgElt) -> SeqEnum[RngIntElt]
  {Converts a string to a list of integers.}
  l := [];
  for i in {1..#str} do
    Append(~l, StringToCode(str[i]));
  end for;
  return l;
end intrinsic;

intrinsic BelyiDBCodeToString(l::SeqEnum[RngIntElt]) -> MonStgElt
  {Converts a list of integers to a string.}
  str := "";
  for i in {1..#l} do
    str *:= CodeToString(l[i]);
  end for;
  return str;
end intrinsic;

intrinsic BelyiDBDeleteLineBreaks(str::MonStgElt) -> MonStgElt
  {Given a string str possibly with line breaks return a string without the line breaks.}
  str_new := "";
  for i in [1..#str] do
    if str[i] ne "\n" then
      str_new *:= str[i];
    end if;
  end for;
  return str_new;
end intrinsic;

intrinsic BelyiDBGenerateName(sigma::SeqEnum[GrpPermElt]) -> MonStgElt
  {Generate a unique string identifying the passport corresponding to sigma.}
  assert #sigma eq 3;
  H := Parent(sigma[1]);
  d := Degree(H);
  G := sub<Sym(d)|sigma>;
  assert IsTransitive(G);
  g,d := TransitiveGroupIdentification(G);
  a,b,c := Explode([Order(sigma[1]), Order(sigma[2]), Order(sigma[3])]);
  if d lt 10 then // JV naming convention
    name := Sprintf("%oT%o-[%o,%o,%o]-", d, g, a, b, c);
    cs0, cs1, csoo := Explode([CycleStructure(sigma[i]) : i in {1..3}]);
    for i in {1..#cs0-1} do
      for j in {1..cs0[i][2]} do
        name *:= Sprintf("%o", cs0[i][1]);
      end for;
    end for;
    for j in {1..cs0[#cs0][2]} do
      name *:= Sprintf("%o", cs0[#cs0][1]);
    end for;
    name *:= "-";
    for i in {1..#cs1-1} do
      for j in {1..cs1[i][2]} do
        name *:= Sprintf("%o", cs1[i][1]);
      end for;
    end for;
    for j in {1..cs1[#cs1][2]} do
      name *:= Sprintf("%o", cs1[#cs1][1]);
    end for;
    name *:= "-";
    for i in {1..#csoo} do
      for j in {1..csoo[i][2]} do
        name *:= Sprintf("%o", csoo[i][1]);
      end for;
    end for;
    c0 := #CycleDecomposition(sigma[1]);
    c1 := #CycleDecomposition(sigma[2]);
    coo := #CycleDecomposition(sigma[3]);
    genus := (d+2-c0-c1-coo)/2;
    name *:= Sprintf("-g%o", genus);
  else // JV d>9 naming convention
    name := Sprintf("%oT%o-[%o,%o,%o]-", d, g, a, b, c);
    cs0, cs1, csoo := Explode([CycleStructure(sigma[i]) : i in {1..3}]);
    for i in {1..#cs0-1} do
      for j in {1..cs0[i][2]} do
        name *:= Sprintf("%o,", cs0[i][1]);
      end for;
    end for;
    for j in {1..cs0[#cs0][2]-1} do
      name *:= Sprintf("%o,", cs0[#cs0][1]);
    end for;
    name *:= Sprintf("%o", cs0[#cs0][1]);
    name *:= "-";
    for i in {1..#cs1-1} do
      for j in {1..cs1[i][2]} do
        name *:= Sprintf("%o,", cs1[i][1]);
      end for;
    end for;
    for j in {1..cs1[#cs1][2]-1} do
      name *:= Sprintf("%o,", cs1[#cs1][1]);
    end for;
    name *:= Sprintf("%o", cs1[#cs1][1]);
    name *:= "-";
    for i in {1..#csoo-1} do
      for j in {1..csoo[i][2]} do
        name *:= Sprintf("%o,", csoo[i][1]);
      end for;
    end for;
    for j in {1..csoo[#csoo][2]-1} do
      name *:= Sprintf("%o,", csoo[#csoo][1]);
    end for;
    name *:= Sprintf("%o", csoo[#csoo][1]);
    c0 := #CycleDecomposition(sigma[1]);
    c1 := #CycleDecomposition(sigma[2]);
    coo := #CycleDecomposition(sigma[3]);
    genus := (d+2-c0-c1-coo)/2;
    name *:= Sprintf("-g%o", genus);
  end if;
  return name;
end intrinsic;

intrinsic BelyiDBGenerateNameAboveTransitiveDatabaseLimit(sigma::SeqEnum[GrpPermElt]) -> MonStgElt
  {Generate a unique string identifying the passport corresponding to sigma where Degree(sigma[1]) > TransitiveGroupDatabaseLimit().}
  assert #sigma eq 3;
  assert Degree(sigma[1]) gt TransitiveGroupDatabaseLimit();
  H := Parent(sigma[1]);
  d := Degree(H);
  G := sub<Sym(d)|sigma>;
  assert IsTransitive(G);
  // g,d := TransitiveGroupIdentification(G);
  a,b,c := Explode([Order(sigma[1]), Order(sigma[2]), Order(sigma[3])]);
  // name := Sprintf("%oT%o-[%o,%o,%o]-", d, g, a, b, c);
  name := Sprintf("%oT-[%o,%o,%o]-", d, a, b, c);
  cs0, cs1, csoo := Explode([CycleStructure(sigma[i]) : i in {1..3}]);
  for i in {1..#cs0-1} do
    for j in {1..cs0[i][2]} do
      name *:= Sprintf("%o,", cs0[i][1]);
    end for;
  end for;
  for j in {1..cs0[#cs0][2]-1} do
    name *:= Sprintf("%o,", cs0[#cs0][1]);
  end for;
  name *:= Sprintf("%o", cs0[#cs0][1]);
  name *:= "-";
  for i in {1..#cs1-1} do
    for j in {1..cs1[i][2]} do
      name *:= Sprintf("%o,", cs1[i][1]);
    end for;
  end for;
  for j in {1..cs1[#cs1][2]-1} do
    name *:= Sprintf("%o,", cs1[#cs1][1]);
  end for;
  name *:= Sprintf("%o", cs1[#cs1][1]);
  name *:= "-";
  for i in {1..#csoo-1} do
    for j in {1..csoo[i][2]} do
      name *:= Sprintf("%o,", csoo[i][1]);
    end for;
  end for;
  for j in {1..csoo[#csoo][2]-1} do
    name *:= Sprintf("%o,", csoo[#csoo][1]);
  end for;
  name *:= Sprintf("%o", csoo[#csoo][1]);
  c0 := #CycleDecomposition(sigma[1]);
  c1 := #CycleDecomposition(sigma[2]);
  coo := #CycleDecomposition(sigma[3]);
  genus := (d+2-c0-c1-coo)/2;
  name *:= Sprintf("-g%o", genus);
  return name;
end intrinsic;

intrinsic BelyiDBFilenames(d::RngIntElt) -> SeqEnum[MonStgElt]
  {Returns the filenames (MonStgElts) in BelyiDB/d as a SeqEnum. This assumes the current directory is BelyiDB. If BelyiDB/d does not exist an empty sequence is returned.}
  // directory stuff
    dir := GetCurrentDirectory();
    parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
    if parentdir eq "BelyiDB\n" then
      dbdirectory := dir;
    else
      error "make sure your working directory is /BelyiDB";
    end if;
    directory := dbdirectory cat Sprintf("/%o/", d);
  // check to see if directory /BelyiDB/d exists
    command := Sprintf("ls");
    ls := Pipe(command, "");
    BelyiDBDirectories := Split(ls, "\n");
    if Sprintf("%o", d) notin BelyiDBDirectories then
      return [];
    end if;
  // get the filenames for some specified degree d
    command := Sprintf("ls %o", d);
    ls := Pipe(command, "");
    filenames := Split(ls, "\n");
    return filenames;
end intrinsic;

intrinsic BelyiDBExample(ppass::SeqEnum[SeqEnum[GrpPermElt]]) -> BelyiDB
  {Creates a BelyiDB object corresponding to pointed passport ppass.}
  // some sanity checks
    assert #ppass gt 0;
    sigma := ppass[1];
    pass := PassportRepresentatives(sigma);
    assert #ppass ge #pass;
    // assert #ppass eq #pass; // just for fun
    d := Degree(Parent(sigma[1]));
    G := sub< Sym(d) | sigma >;
    assert IsTransitive(G);
    assert Parent(ppass[1][1]) eq G;
  // BelyiDBName
    if Degree(sigma[1]) gt TransitiveGroupDatabaseLimit() then
      error "group not in transitive database!";
    else
      newname := BelyiDBGenerateName(sigma);
    end if;
  // create one BelyiDB per passport
    s := BelyiDBInitialize();
  // easy attrs
    s`BelyiDBName := newname;
    s`BelyiDBFilename := newname cat ".m";
    s`BelyiDBDegree := d;
    s`BelyiDBOrders := [Order(sigma[i]) : i in {1..3}];
    // BelyiDBType
      a,b,c := Explode(s`BelyiDBOrders);
      if 1/a+1/b+1/c gt 1 then
        s`BelyiDBType := "Spherical";
      elif 1/a+1/b+1/c eq 1 then
        s`BelyiDBType := "Euclidean";
      else
        s`BelyiDBType := "Hyperbolic";
      end if;
    // BelyiDBGenus
      c0 := #CycleDecomposition(sigma[1]);
      c1 := #CycleDecomposition(sigma[2]);
      coo := #CycleDecomposition(sigma[3]);
      genus := (d+2-c0-c1-coo)/2;
      s`BelyiDBGenus := genus;
    s`BelyiDBSize := #pass;
    s`BelyiDBPointedSize := #ppass;
  // permutation attrs
    s`BelyiDBPermutationTriple := sigma;
    // BelyiDBAutomorphismGroup
    s`BelyiDBAutomorphismGroup := AutomorphismGroup(sigma);
    s`BelyiDBPointedAutomorphismGroup := PointedAutomorphismGroup(sigma);
    s`BelyiDBMonodromyGroup := G;
    s`BelyiDBPassport := pass;
    s`BelyiDBPointedPassport := ppass;
    // s`BelyiDBGaloisOrbits computed later
  return s;
end intrinsic;

intrinsic BelyiDBPlaceIndex(base_field_data::List) -> RngIntElt
  {returns integer that records the infinite place of a number field.}
  K := base_field_data[1];
  Kv := base_field_data[2];
  places := InfinitePlaces(K);
  for i := 1 to #places do
    if places[i] eq Kv then
      return i;
    end if;
  end for;
  error "Didn't find a place!";
end intrinsic;

intrinsic VarText(var::MonStgElt, lower::RngIntElt, upper::RngIntElt) -> MonStgElt
  {returns text "varlower, varlower+1, ..., varupper-1, varupper".}
  assert upper ge lower;
  var_text := "";
  if upper eq lower then
    var_text *:= Sprintf("%o%o", var, lower);
  else
    for i := lower to upper-1 by 1 do
      var_text *:= Sprintf("%o%o, ", var, i);
    end for;
    var_text *:= Sprintf("%o%o", var, upper);
  end if;
  return var_text;
end intrinsic;

intrinsic BelyiDBVarText(var::MonStgElt, lower::RngIntElt, upper::RngIntElt) -> MonStgElt
  {returns text "varlower, varlower+1, ..., varupper-1, varupper".}
  assert upper ge lower;
  var_text := "";
  if upper eq lower then
    var_text *:= Sprintf("\"%o%o\"", var, lower);
  else
    for i := lower to upper-1 by 1 do
      var_text *:= Sprintf("\"%o%o\", ", var, i);
    end for;
    var_text *:= Sprintf("\"%o%o\"", var, upper);
  end if;
  return var_text;
end intrinsic;

intrinsic BelyiDBBaseFieldDataWriter(base_field_data::List, i::RngIntElt) -> MonStgElt
  {text to load base field data.}
  K := base_field_data[1];
  Kv := base_field_data[2];
  conj := base_field_data[3];
  z := base_field_data[4];
  assert ISA(Type(K), FldNum) or ISA(Type(K), FldRat);
  assert ISA(Type(Kv), PlcNumElt);
  assert ISA(Type(conj), BoolElt);
  // text for K
  gens := GeneratorsSequence(K);
  assert #gens eq 1;
  if AbsoluteDegree(K) eq 1 then
    str := Sprintf("K%o<nu%o> := RationalsAsNumberField();\n", i, i);
  else
    str := Sprintf("K%o<nu%o> := NumberField(%m);\n", i, i, MinimalPolynomial(K.1));
  end if;
  // text for Kv
  plc_ind := BelyiDBPlaceIndex(base_field_data);
  str *:= Sprintf("place%o := InfinitePlaces(K%o)[%o];\n", i, i, plc_ind);
  // text for conj
  str *:= Sprintf("conj%o := %m;\n", i, conj);
  // text for z
  CC<I> := ComplexField(Precision(Parent(z)));
  str *:= Sprintf("CC<I> := ComplexField(%o);\n", Precision(Parent(z)));
  str *:= Sprintf("z%o := %m;\n", i, z);
  // append
  str *:= Sprintf("base_field_data_%o := [* K%o, place%o, conj%o, z%o *];\n", i, i, i, i, i);
  return str;
end intrinsic;

intrinsic BelyiDBBelyiMapWriter(base_field_data::List, X::Crv, phi::FldFunFracSchElt, i::RngIntElt) -> MonStgElt
  {text to load curve and Belyi map.}
  // base field data
    K := base_field_data[1];
    Kv := base_field_data[2];
    conj := base_field_data[3];
    z := base_field_data[4];
  // assertions
    curve_field := BaseField(X);
    map_field := BaseField(Curve(Parent(phi)));
    assert curve_field eq map_field;
    if Type(curve_field) eq FldNum then
      assert GeneratorsSequence(curve_field) eq GeneratorsSequence(map_field);
      assert #GeneratorsSequence(curve_field) eq #GeneratorsSequence(K);
    end if;
    assert ISA(Type(K), FldNum) or ISA(Type(K), FldRat);
    assert ISA(Type(Kv), PlcNumElt);
    assert ISA(Type(conj), BoolElt);
    KX := FunctionField(X);
    assert Parent(phi) eq KX;
  // text to make Xi and phii cases by genus
  str := "";
  if Genus(X) eq 0 then
    // Genus 0 case
    assert Sprintf("%o", KX.1) eq "x";
    str *:= Sprintf("X%o := Curve(ProjectiveSpace(PolynomialRing(K%o, 2)));\n", i, i);
    str *:= Sprintf("KX%o<x> := FunctionField(X%o);\n", i, i);
    str *:= Sprintf("phi%o := KX%o!(%o);\n", i, i, phi);
  else
    if Type(X) in [CrvHyp, CrvEll] then
      if Type(X) eq CrvEll then
        // EllipticCurve case
        aInvs := aInvariants(X);
        str *:= BelyiDBDeleteLineBreaks(Sprintf("aInvs%o := %o;\n", i, aInvs)) cat "\n";
        str *:= Sprintf("E%o := EllipticCurve(aInvs%o);\n", i, i);
        str *:= Sprintf("X%o := BaseChange(E%o, K%o);\n", i, i, i);
        assert Sprintf("%o", KX.1) eq "x";
        assert Sprintf("%o", KX.2) eq "y";
        str *:= Sprintf("KX%o<%o,%o> := FunctionField(X%o);\n", i, KX.1, KX.2, i);
        str *:= Sprintf("phi%o := KX%o!(%o);\n", i, i, phi);
      else
        // Hyperelliptic case (non Elliptic)
        f, h := HyperellipticPolynomials(X);
        P := Parent(f);
        AssignNames(~P, ["x"]);
        str *:= Sprintf("P<x> := PolynomialRing(K%o);\n", i);
        str *:= Sprintf("X%o := HyperellipticCurve(%o, %o);\n", i, f, h);
        assert Sprintf("%o", KX.1) eq "x";
        assert Sprintf("%o", KX.2) eq "y";
        str *:= Sprintf("KX%o<%o,%o> := FunctionField(X%o);\n", i, KX.1, KX.2, i);
        str *:= Sprintf("phi%o := KX%o!(%o);\n", i, i, phi);
      end if;
    else
      // make ambient for Xi
      ambient := Ambient(X);
      num_vars := Dimension(ambient);
      vars := eval Sprintf("[%o]", BelyiDBVarText("x", 1, num_vars+1));
      AssignNames(~ambient, vars);
      str *:= Sprintf("ambient%o<%o> := ProjectiveSpace(K%o, %o);\n", i, VarText("x", 1, num_vars+1), i, num_vars);
      str *:= Sprintf("AssignNames(~ambient%o, [%o]);\n", i, BelyiDBVarText("x", 1, num_vars+1));
      // Xi
      str *:= Sprintf("X%o<%o> := Curve(ambient%o, %o);\n", i, VarText("x", 1, num_vars+1), i, DefiningEquations(X));
      // phii
      error "for general curves, writing BelyiMap to file not implemented yet.";
    end if;
  end if;
  // return
  return str;
end intrinsic;

intrinsic BelyiDBExactWriter(l::SeqEnum, index::RngIntElt) -> MonStgElt
  {returns text to load a sequence l of elements of Kindex.}
  str := Sprintf("[K%o | \n", index);
  for i in [1..#l-1] do
    str *:= Sprintf("%o,\n", Eltseq(l[i]));
  end for;
  str *:= Sprintf("%o\n]", Eltseq(l[#l]));
  return str;
end intrinsic;

intrinsic BelyiDBExactWriter(l::List) -> MonStgElt
  {l[1] has exact elements, l[2] has K_list where the elements live, and this intrinsic returns text to load l[1].}
  assert #l eq 2;
  K_list := l[2];
  l := l[1];
  assert #K_list eq #l;
  str := "[*\n";
  for i in [1..#l-1] do
    str *:= BelyiDBExactWriter(l[i], i);
    str *:= ",\n";
  end for;
  str *:= BelyiDBExactWriter(l[#l], #l);
  str *:= "\n*]";
  return str;
end intrinsic;

intrinsic BelyiDBText(s::BelyiDB) -> MonStgElt
  {Create (magma-loadable) text for BelyiDB object.}
  // setup
    SetColumns(0);
    str := "s := BelyiDBInitialize();\n";
  // %m attributes
    all_attrs := GetAttributes(Type(s));
    automatic_attrs := []; // can be printed using %m
    Append(~automatic_attrs, "BelyiDBName");
    Append(~automatic_attrs, "BelyiDBFilename");
    Append(~automatic_attrs, "BelyiDBDegree");
    Append(~automatic_attrs, "BelyiDBOrders");
    Append(~automatic_attrs, "BelyiDBType");
    Append(~automatic_attrs, "BelyiDBGenus");
    Append(~automatic_attrs, "BelyiDBSize");
    Append(~automatic_attrs, "BelyiDBPointedSize");
    Append(~automatic_attrs, "BelyiDBPermutationTriple");
    Append(~automatic_attrs, "BelyiDBAutomorphismGroup");
    Append(~automatic_attrs, "BelyiDBPointedAutomorphismGroup");
    Append(~automatic_attrs, "BelyiDBMonodromyGroup");
    Append(~automatic_attrs, "BelyiDBPassport");
    Append(~automatic_attrs, "BelyiDBPointedPassport");
    Append(~automatic_attrs, "BelyiDBGaloisOrbits");
  // exact attributes
    exact_attrs := [];
    Append(~exact_attrs, "BelyiDBExactCurveInvariants");
    Append(~exact_attrs, "BelyiDBExactCurveCoefficients");
    Append(~exact_attrs, "BelyiDBExactBelyiMapLeadingCoefficients");
    Append(~exact_attrs, "BelyiDBExactBelyiMapNumeratorCoefficients");
    Append(~exact_attrs, "BelyiDBExactBelyiMapDenominatorCoefficients");
  // write text for %m attributes
    str *:= "\n/*\nBasic Information about the Passport\n*/\n\n";
    for attr in automatic_attrs do
      if assigned s``attr then
        str *:= Sprintf("s`%o := ", attr);
        str *:= Sprintf("%m;\n", s``attr);
      end if;
    end for;
  // BelyiDBBaseFieldData, [* [* K, Kv, conj, complex embeddding *],... *]
    str *:= "\n/*\nBase Field Data\n*/\n\n";
    if assigned s`BelyiDBBaseFieldData then
      assert assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps;
      assert #s`BelyiDBBaseFieldData eq #s`BelyiDBPointedPassport;
      // base field data list will contain base_field_data_i
      str *:= "base_field_data := [* *];\n";
      for i := 1 to #s`BelyiDBBaseFieldData do
        // makes text for base_field_data_i
        str *:= BelyiDBBaseFieldDataWriter(s`BelyiDBBaseFieldData[i], i);
        // append base_field_data_i to base_field_data
        str *:= Sprintf("Append(~base_field_data, base_field_data_%o);\n", i);
      end for;
      str *:= Sprintf("s`BelyiDBBaseFieldData := base_field_data;\n");
    end if;
  // BelyiDBBelyiCurves and BelyiDBBelyiMaps
    str *:= "\n/*\nBelyi Maps\n*/\n\n";
    if assigned s`BelyiDBBelyiMaps then
      assert assigned s`BelyiDBBaseFieldData and assigned s`BelyiDBBelyiCurves;
      assert #s`BelyiDBBelyiMaps eq #s`BelyiDBPointedPassport;
      assert #s`BelyiDBBelyiCurves eq #s`BelyiDBPointedPassport;
      // curves list will contain Xi
      str *:= "curves := [* *];\n";
      // maps list will contain phii
      str *:= "maps := [* *];\n";
      for i := 1 to #s`BelyiDBBelyiMaps do
        base_field_data := s`BelyiDBBaseFieldData[i];
        str *:= Sprintf("K := K%o;\n", i);
        X := s`BelyiDBBelyiCurves[i];
        phi := s`BelyiDBBelyiMaps[i];
        str *:= BelyiDBBelyiMapWriter(base_field_data, X, phi, i);
        // append curve_i to curves
        str *:= Sprintf("Append(~curves, X%o);\n", i);
        // append map_i to maps
        str *:= Sprintf("Append(~maps, phi%o);\n", i);
      end for;
      str *:= Sprintf("s`BelyiDBBelyiCurves := curves;\n");
      str *:= Sprintf("s`BelyiDBBelyiMaps := maps;\n");
    end if;
  // exact
    str *:= "\n/*\nExact Data\n*/\n\n";
    for i := 1 to #exact_attrs do
      attr := exact_attrs[i];
      if assigned s``attr then
        assert Type(s``attr) eq List;
        assert assigned s`BelyiDBBaseFieldData; // needed in BelyiDBExactWriter
        l := [* s``attr, s`BelyiDBBaseFieldData *]; // input to BelyiDBExactWriter needs base field data
        str *:= Sprintf("s`%o := %o;\n", attr, BelyiDBExactWriter(l));
        str *:= Sprintf("s`%o := [* s`%o, s`BelyiDBBaseFieldData *];\n", attr, attr);
      end if;
    end for;
  // numerical
    str *:= "\n/*\nNumerical Data\n*/\n\n";
    if assigned s`BelyiDBRescalingFactors then
      str *:= Sprintf("CC<I> := ComplexField(%o);\n", Precision(Parent(s`BelyiDBRescalingFactors[1])));
      str *:= Sprintf("s`BelyiDBRescalingFactors := %m;\n", s`BelyiDBRescalingFactors);
    end if;
  // BelyiDBPowserBases
    str *:= "\n/*\nPowser Bases\n*/\n\n";
    if assigned s`BelyiDBPowserBases then
      indat := s`BelyiDBPowserIndat;
      pows := s`BelyiDBPowserBases;
      pow := pows[1][1];
      str *:= Sprintf("CC<I> := ComplexField(%o);\n", Precision(BaseRing(Parent(pow))));
      str *:= Sprintf("Ser<w> := PowerSeriesRing(CC, %o);\n", Precision(Parent(pow)));
      str *:= Sprintf("s`BelyiDBPowserIndat := %m;\n", indat);
      str *:= Sprintf("s`BelyiDBPowserBases := [];\n");
      for i := 1 to #pows do
        str *:= Sprintf("expansions := [];\n");
        for j := 1 to #pows[i] do
          str *:= Sprintf("Append(~expansions, Ser!(%m));\n", Eltseq(pows[i][j]));
        end for;
        str *:= Sprintf("Append(~s`BelyiDBPowserBases, expansions);\n");
      end for;
    end if;
  // return statement for eval fuction and writing
    str *:= "\n/*\nReturn for eval\n*/\n\n";
    str *:= Sprintf("return s;");
  return str;
end intrinsic;

intrinsic BelyiDBWrite(s::BelyiDB) -> MonStgElt
  {Write BelyiDBText information to the proper file.}
  // this eliminates automatic line breaks while printing
    SetColumns(0);
  // directory stuff
    dir := GetCurrentDirectory();
    parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
    if parentdir eq "BelyiDB\n" then
      dbdirectory := dir;
    else
      error "make sure your working directory is /BelyiDB";
    end if;
  // makes sure the object has some basic information
    if assigned s`BelyiDBDegree and assigned s`BelyiDBName then
      d := s`BelyiDBDegree;
      directory := dbdirectory cat Sprintf("/%o", d);
      name := s`BelyiDBName;
      filename := s`BelyiDBFilename;
      savedir := Sprintf(directory cat "/%o" cat ".m", name);
    else
      error "this BelyiDB object does not have enough information worth saving!";
    end if;
  // BelyiDBText
    str := BelyiDBText(s);
  // write to file
    Write(savedir, str : Overwrite := true);
    returnText := Sprintf("%o written in directory %o\n", filename, directory);
    return returnText;
end intrinsic;

intrinsic BelyiDBGenerate(d::RngIntElt) -> MonStgElt
  {Creates the folder /d in BelyiDB with all BelyiDB files for degree d. This assumes the current directory is /BelyiDB.}
  // directory stuff
    dir := GetCurrentDirectory();
    parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
    if parentdir eq "BelyiDB\n" then
      dbdirectory := dir;
    else
      error "make sure your working directory is /BelyiDB";
    end if;
    directory := dbdirectory cat Sprintf("/%o/", d);
    System(Sprintf("mkdir %o", d)); // if directory already exists this throws a system error but all good
    System(Sprintf("chmod 777 %o", d)); // set permissions for directory
  // generate all degree d passports
  db := TransitiveGroups(d);
  for G in db do
    ppassesG := PassportRepresentatives(G : Pointed := true);
    for j in {1..#ppassesG} do // j indexes the passports of a group
      ppass := ppassesG[j][2]; // this is a single passport
      s := BelyiDBExample(ppass);
      // write the object to file
      BelyiDBWrite(s);
    end for;
  end for;
  returnText := Sprintf("BelyiDB for degree %o constructed in directory %o/%o\n", d, dbdirectory, d);
  return returnText;
end intrinsic;

intrinsic BelyiDBMatch(s::BelyiDB) -> BoolElt
  {True if name of s appears in database. This assumes the working directory is /BelyiDB.}
  // pull information from s
    d := s`BelyiDBDegree;
    sfilename := s`BelyiDBFilename;
  // directory stuff
    dir := GetCurrentDirectory();
    parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
    if parentdir eq "BelyiDB\n" then
      dbdirectory := dir;
    else
      error "make sure your working directory is /BelyiDB";
    end if;
    directory := dbdirectory cat Sprintf("/%o/", d);
  // check to see if directory /BelyiDB/d exists
    command := Sprintf("ls");
    ls := Pipe(command, "");
    BelyiDBDirectories := Split(ls, "\n");
    if Sprintf("%o", d) notin BelyiDBDirectories then
      return false;
    end if;
  // get the filenames for some specified degree d
    command := Sprintf("ls %o", d);
    ls := Pipe(command, "");
    filenames := Split(ls, "\n");
    if sfilename in filenames then
      return true;
    else
      return false;
    end if;
end intrinsic;

intrinsic BelyiMapSanityCheck(s::BelyiDB : lax := false) -> Any
  {overloaded for BelyiDB.}
  if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps and assigned s`BelyiDBPointedPassport then
    assert assigned s`BelyiDBBelyiCurves;
    assert assigned s`BelyiDBBelyiMaps;
    assert #s`BelyiDBPointedPassport eq #s`BelyiDBBelyiCurves;
    assert #s`BelyiDBPointedPassport eq #s`BelyiDBBelyiMaps;
    pass := s`BelyiDBPointedPassport;
    curves := s`BelyiDBBelyiCurves;
    maps := s`BelyiDBBelyiMaps;
    // list in case we set lax true
    for i in [1..#pass] do
      sane := BelyiMapSanityCheck(pass[i], curves[i], maps[i] : lax := lax);
      if not sane then
        return false;
      end if;
    end for;
    return true;
  else
    return false;
  end if;
end intrinsic;

intrinsic BelyiDBToGammas(s::BelyiDB) -> SeqEnum[GrpPSL2]
  {Creates a sequence of GrpPSL2s from a BelyiDB object.}
  assert s`BelyiDBType eq "Hyperbolic";
  ppass := s`BelyiDBPointedPassport;
  Gammas := [];
  for sigma in ppass do
    lcm := LeastCommonMultiple(s`BelyiDBOrders);
    vprint Shimura : Sprintf("\nComputing Gamma with LCM(a,b,c) = %o...\n", lcm);
    if lcm lt 100 then // TODO this is a bit of a hack
      Gamma := TriangleSubgroup(sigma);
    else
      Gamma := TriangleSubgroup(sigma : Simplify := 0);
    end if;
    Append(~Gammas, Gamma);
  end for;
  return Gammas;
end intrinsic;

intrinsic GammasToBelyiDB(Gammas::SeqEnum[GrpPSL2]) -> BelyiDB
  {Assumes Gammas have everything computed and creates a BelyiDB object with sanity checks.}
  // setup
    ppass := [];
    for i := 1 to #Gammas do
      Append(~ppass, Gammas[i]`TriangleSigma);
    end for;
    s := BelyiDBExample(ppass);
  // easy attrs assertions
    for Gamma in Gammas do
      assert s`BelyiDBOrders eq Gamma`TriangleABC;
    end for;
    assert s`BelyiDBType eq "Hyperbolic";
    for Gamma in Gammas do
      assert s`BelyiDBGenus eq Genus(Gamma);
    end for;
    assert s`BelyiDBSize le s`BelyiDBPointedSize;
    assert s`BelyiDBPointedSize eq #Gammas;
  // permutation attrs assertions
    for Gamma in Gammas do
      assert sub< Sym(Gamma`TriangleD) | Gamma`TriangleSigma > eq s`BelyiDBMonodromyGroup;
    end for;
  // BelyiMaps
    base_field_data := [* *];
    curves := [* *];
    maps := [* *];
    for i := 1 to #Gammas do
      Gamma := Gammas[i];
      K := Gamma`TriangleK;
      Kv := Gamma`TriangleKv;
      conj := Gamma`TriangleKIsConjugated;
      z := Gamma`TriangleKNumericalGenerator;
      Append(~base_field_data, [* K, Kv, conj, z *]);
      Append(~curves, Gamma`TriangleBelyiCurve);
      Append(~maps, Gamma`TriangleBelyiMap);
    end for;
    s`BelyiDBBaseFieldData := base_field_data;
    s`BelyiDBBelyiCurves := curves;
    s`BelyiDBBelyiMaps := maps;
    assert #SequenceToSet([#s`BelyiDBBaseFieldData, #s`BelyiDBBelyiCurves, #s`BelyiDBBelyiMaps, #s`BelyiDBPointedPassport]) eq 1;
  // Galois orbits
    s := BelyiDBGaloisOrbitsComputer(s);
  // exact attrs
    exact_attrs := [];
    Append(~exact_attrs, "BelyiDBExactCurveInvariants");
    Append(~exact_attrs, "BelyiDBExactCurveCoefficients");
    Append(~exact_attrs, "BelyiDBExactBelyiMapLeadingCoefficients");
    Append(~exact_attrs, "BelyiDBExactBelyiMapNumeratorCoefficients");
    Append(~exact_attrs, "BelyiDBExactBelyiMapDenominatorCoefficients");
    for attr in exact_attrs do
      s``attr := [* *];
    end for;
    for Gamma in Gammas do
      // might not be assigned to Gamma
      // FIXME bool instead of deleting attribute of s
      if assigned Gamma`TriangleExactCurveInvariants then
        Append(~s`BelyiDBExactCurveInvariants, Gamma`TriangleExactCurveInvariants);
      else
        delete s`BelyiDBExactCurveInvariants;
      end if;
      if assigned Gamma`TriangleExactCurveCoefficients then
        Append(~s`BelyiDBExactCurveCoefficients, Gamma`TriangleExactCurveCoefficients);
      else
        delete s`BelyiDBExactCurveCoefficients;
      end if;
      // should always be assigned
      lc := Gamma`TriangleExactBelyiMapLeadingCoefficient;
      dens := Gamma`TriangleExactBelyiMapDenominatorCoefficients;
      nums := Gamma`TriangleExactBelyiMapNumeratorCoefficients;
      // assertions!
      assert #dens gt 0;
      assert #nums gt 0;
      assert #[lc] gt 0;
      // printf "LEADING COEFF for Gammas[%o] for %o = \n%o\n", Index(Gammas, Gamma), s`BelyiDBName, lc;
      // printf "DENOM COEFFS for Gammas[%o] for %o = \n%o\n", Index(Gammas, Gamma), s`BelyiDBName, dens;
      assert Type([lc]) eq Type(dens); // Gamma doesn't have correct data to be written to file
      assert Type([lc][1]) eq Type(dens[1]); // Gamma doesn't have correct data to be written to file
      Append(~s`BelyiDBExactBelyiMapLeadingCoefficients, [Gamma`TriangleExactBelyiMapLeadingCoefficient]);
      Append(~s`BelyiDBExactBelyiMapNumeratorCoefficients, Gamma`TriangleExactBelyiMapNumeratorCoefficients);
      Append(~s`BelyiDBExactBelyiMapDenominatorCoefficients, Gamma`TriangleExactBelyiMapDenominatorCoefficients);
    end for;
  // numerical attrs
    s`BelyiDBRescalingFactors := [* *];
    all_rescaling_factors_assigned := true;
    for Gamma in Gammas do
      if assigned Gamma`TriangleRescalingFactor then
        Append(~s`BelyiDBRescalingFactors, Gamma`TriangleRescalingFactor);
      else
        all_rescaling_factors_assigned := false;
      end if;
    end for;
    if not all_rescaling_factors_assigned then
      delete s`BelyiDBRescalingFactors;
    end if;
  // Powser
    assert assigned Gamma`TrianglePowserBases;
    s`BelyiDBPowserIndat := Gamma`TrianglePowserBases[1][1];
    s`BelyiDBPowserBases := Gamma`TrianglePowserBases[1][2][1];
  // TODO assertions
  /* pick attributes to check are assigned
    attrs := GetAttributes(Type(s));
    for attr in attrs do
      assert assigned s``attr;
    end for;
  */
    assert BelyiMapSanityCheck(s);
    assert BelyiDBMatch(s);
  // return
    return s;
end intrinsic;

intrinsic BelyiDBCompareBelyiMaps(f::FldFunFracSchElt, g::FldFunFracSchElt) -> BoolElt
  {True is f and g are the same "up to base field".}
  // TODO assert base fields equal
  num_f := Coefficients(Numerator(f));
  num_g := Coefficients(Numerator(g));
  den_f := Coefficients(Denominator(f));
  den_g := Coefficients(Denominator(g));
  if #num_f ne #num_g or #den_f ne #den_f then
    return false;
  else
    for i := 1 to #num_f do
      if Eltseq(num_f[i]) ne Eltseq(num_g[i]) then
        return false;
      end if;
    end for;
    for i := 1 to #den_f do
      if Eltseq(den_f[i]) ne Eltseq(den_g[i]) then
        return false;
      end if;
    end for;
    return true;
  end if;
end intrinsic;

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

// TODO make g0 automagic (makeshift GaloisOrbits adjusting for smaller m and ByRam when Newton breaks)
intrinsic BelyiMap(s::BelyiDB : prec := 0, Al := "Newton") -> BelyiDB
  {wrapper to use with BelyiDB objects.}
  if s`BelyiDBType ne "Hyperbolic" then
    error "Nonhyperbolic!";
  else
    Gammas := BelyiDBToGammas(s);
    if s`BelyiDBGenus eq 0 then
      // DegreeBound automated
      for Gamma in Gammas do
        for m := #s`BelyiDBPointedPassport to 1 by -1 do
          try
            BelyiMap(Gamma : prec := prec, DegreeBound := m);
          catch e
            vprintf Shimura : "%o button did not work error: %o\n", s`BelyiDBName, e;
            vprintf Shimura : "%o try DegreeBound = %o\n", s`BelyiDBName, m-1;
          end try;
          if not assigned Gamma`TriangleBelyiMap or not assigned Gamma`TriangleBelyiCurve or not assigned Gamma`TriangleK then
            vprintf Shimura : "%o try ByRamification with prec = %o\n", s`BelyiDBName, 2*prec;
            try
              BelyiMap(Gamma : prec := 2*prec, Al := "ByRamification");
            catch e
              vprintf Shimura : "%o button did not work error: %o\n", s`BelyiDBName, e;
            end try;
          end if;
          if assigned Gamma`TriangleBelyiMap and assigned Gamma`TriangleBelyiCurve and assigned Gamma`TriangleK then
            break m;
          end if;
        end for;
      end for;
    end if;
    if s`BelyiDBGenus eq 1 then
      // CHANGE THIS IF GALOIS ORBITS NEWTON WORKS input Gammas
      try_bool := true;
      for i := 1 to #Gammas do
        Gamma := Gammas[i];
        if try_bool then
          try
            BelyiMap(Gamma : prec := prec);
          catch e
            vprintf Shimura : "%o button did not work error: %o\n", s`BelyiDBName, e;
            try_bool := false;
          end try;
        end if;
      end for;
    end if;
    if s`BelyiDBGenus gt 1 then
      try
        BelyiMap(Gammas : Al := "NumericalKernel", ExactAl := "GaloisOrbits", prec := prec);
      catch e
        vprintf Shimura : "%o button did not work error: %o\n", s`BelyiDBName, e;
      end try;
    end if;
    s := GammasToBelyiDB(Gammas);
    if BelyiMapSanityCheck(s) then
      return s;
    else
      error "failed sanity check";
    end if;
  end if;
end intrinsic;

intrinsic BelyiMapNonhyp(s::BelyiDB) -> BelyiDB
  {}
  assert s`BelyiDBType ne "Hyperbolic";
  ppass := s`BelyiDBPointedPassport;
  curves := [* *];
  maps := [* *];
  for sigma in ppass do
    X, phi := BelyiMap(sigma);
    assert BelyiMapSanityCheck(sigma, X, phi);
    Append(~curves, X);
    Append(~maps, phi);
  end for;
  s`BelyiDBBelyiCurves := curves;
  s`BelyiDBBelyiMaps := maps;
  return s;
end intrinsic;

intrinsic BelyiDBSanityCheck(d::RngIntElt) -> Any
  {}
  f := BelyiDBFilenames(d);
  incorrect_map := [];
  checked := [];
  for i := 1 to #f do
    s := BelyiDBRead(f[i]);
    if assigned s`BelyiDBBelyiCurves then
      if not BelyiMapSanityCheck(s) then
        Append(~incorrect_map, s);
      end if;
    end if;
    BelyiDBWrite(s);
    s := BelyiDBRead(f[i]);
    Append(~checked, s);
  end for;
  return checked, f, incorrect_map;
end intrinsic;

intrinsic BelyiDBStatusReport(d::RngIntElt : return_everything := false, return_hyp_notcomputed := true) -> Any
  {This assumes the current directory is /BelyiDB. Returns a string with information about BelyiMaps in /BelyiDB of degree d. This can easily be modified to give lots of information but for now is pretty minimal.}
  // directory stuff
  dir := GetCurrentDirectory();
  parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
  if parentdir eq "BelyiDB\n" then
    dbdirectory := dir;
  else
    error "make sure your working directory is /BelyiDB";
  end if;
  directory := dbdirectory cat Sprintf("/%o/", d);
  f := BelyiDBFilenames(d);
  info := "";
  genus0 := [];
  genus1 := [];
  genus2 := [];
  genus3 := [];
  highergenus := [];
  for i in {1..#f} do
    vprintf Shimura : "%o: (%o/%o)\n", f[i], i, #f;
    s := BelyiDBRead(f[i]);
    if s`BelyiDBGenus eq 0 then
      Append(~genus0, s);
    else
      if s`BelyiDBGenus eq 1 then
        Append(~genus1, s);
      else
        if s`BelyiDBGenus eq 2 then
          Append(~genus2, s);
        else
          if s`BelyiDBGenus eq 3 then
            Append(~genus3, s);
          else
            Append(~highergenus, s);
          end if;
        end if;
      end if;
    end if;
  end for;
  // g0
    g0nonhyp := [];
    g0nonhyp_notcomputed := [];
    g0nonhyp_computed := [];
    g0nonhyp_failedlaxsanity := [];
    g0hyp := [];
    g0hyp_notcomputed := [];
    g0hyp_computed := [];
    g0hyp_failedsanity := [];
  // g1
    g1nonhyp := [];
    g1nonhyp_notcomputed := [];
    g1nonhyp_computed := [];
    g1nonhyp_failedlaxsanity := [];
    g1hyp := [];
    g1hyp_notcomputed := [];
    g1hyp_computed := [];
    g1hyp_failedsanity := [];
  // g2
    g2nonhyp := [];
    g2nonhyp_notcomputed := [];
    g2nonhyp_computed := [];
    g2nonhyp_failedlaxsanity := [];
    g2hyp := [];
    g2hyp_notcomputed := [];
    g2hyp_computed := [];
    g2hyp_failedsanity := [];
  // g3
    g3nonhyp := [];
    g3nonhyp_notcomputed := [];
    g3nonhyp_computed := [];
    g3nonhyp_failedlaxsanity := [];
    g3hyp := [];
    g3hyp_notcomputed := [];
    g3hyp_computed := [];
    g3hyp_failedsanity := [];
  // gg
    ggnonhyp := [];
    ggnonhyp_notcomputed := [];
    ggnonhyp_computed := [];
    ggnonhyp_failedlaxsanity := [];
    gghyp := [];
    gghyp_notcomputed := [];
    gghyp_computed := [];
    gghyp_failedsanity := [];
  for i := 1 to #genus0 do
    s := genus0[i];
    vprintf Shimura : "genus 0 sanity checks: (%o/%o)\n", i, #genus0;
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~g0hyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~g0hyp_computed, s);
        if not BelyiMapSanityCheck(s) then
          Append(~g0hyp_failedsanity, s);
        end if;
      else
        // hyperbolic and belyi maps not computed
        Append(~g0hyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~g0nonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~g0nonhyp_computed, s);
        sanity := BelyiMapSanityCheck(s : lax := true);
        if not sanity then
          Append(~g0nonhyp_failedsanity, s);
        end if;
      else
        // nonhyperbolic and belyi maps not computed
        Append(~g0nonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  for i := 1 to #genus1 do
    s := genus1[i];
    vprintf Shimura : "genus 1 sanity checks: (%o/%o)\n", i, #genus1;
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~g1hyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~g1hyp_computed, s);
        sanity := BelyiMapSanityCheck(s);
        if not sanity then
          Append(~g1hyp_failedsanity, s);
        end if;
      else
        // hyperbolic and belyi maps not computed
        Append(~g1hyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~g1nonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~g1nonhyp_computed, s);
        sanity := BelyiMapSanityCheck(s : lax := true);
        if not sanity then
          Append(~g1nonhyp_failedsanity, s);
        end if;
      else
        // nonhyperbolic and belyi maps not computed
        Append(~g1nonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  for i := 1 to #genus2 do
    s := genus2[i];
    vprintf Shimura : "genus 2 sanity checks: (%o/%o)\n", i, #genus2;
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~g2hyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~g2hyp_computed, s);
        sanity := BelyiMapSanityCheck(s);
        if not sanity then
          Append(~g2hyp_failedsanity, s);
        end if;
      else
        // hyperbolic and belyi maps not computed
        Append(~g2hyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~g2nonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~g2nonhyp_computed, s);
        sanity := BelyiMapSanityCheck(s : lax := true);
        if not sanity then
          Append(~g2nonhyp_failedsanity, s);
        end if;
      else
        // nonhyperbolic and belyi maps not computed
        Append(~g2nonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  for i := 1 to #genus3 do
    s := genus3[i];
    vprintf Shimura : "genus 3 sanity checks: (%o/%o)\n", i, #genus3;
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~g3hyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~g3hyp_computed, s);
        sanity := BelyiMapSanityCheck(s);
        if not sanity then
          Append(~g3hyp_failedsanity, s);
        end if;
      else
        // hyperbolic and belyi maps not computed
        Append(~g3hyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~g3nonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~g3nonhyp_computed, s);
        sanity := BelyiMapSanityCheck(s : lax := true);
        if not sanity then
          Append(~g3nonhyp_failedsanity, s);
        end if;
      else
        // nonhyperbolic and belyi maps not computed
        Append(~g3nonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  for i := 1 to #highergenus do
    s := highergenus[i];
    vprintf Shimura : "higher genus sanity checks: (%o/%o)\n", i, #highergenus;
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~gghyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~gghyp_computed, s);
        sanity := BelyiMapSanityCheck(s);
        if not sanity then
          Append(~gghyp_failedsanity, s);
        end if;
      else
        // hyperbolic and belyi maps not computed
        Append(~gghyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~ggnonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~ggnonhyp_computed, s);
        sanity := BelyiMapSanityCheck(s : lax := true);
        if not sanity then
          Append(~ggnonhyp_failedsanity, s);
        end if;
      else
        // nonhyperbolic and belyi maps not computed
        Append(~ggnonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  // g0
    info *:= Sprintf("%o passport(s) of degree %o in BelyiDB/%o:\n", #f, d, d);
    assert #genus0 eq #g0hyp+#g0nonhyp;
    info *:= Sprintf("  %o genus 0:\n", #g0nonhyp+#g0hyp);
    info *:= Sprintf("    %o nonhyperbolic:\n", #g0nonhyp);
    info *:= Sprintf("      %o not computed.\n", #g0nonhyp_notcomputed);
    info *:= Sprintf("      %o computed:\n", #g0nonhyp_computed);
    // info *:= Sprintf("        %o failed lax sanity.\n", #g0nonhyp_failedlaxsanity);
    info *:= Sprintf("        %o failed sanity.\n", #g0nonhyp_failedlaxsanity);
    info *:= Sprintf("    %o hyperbolic:\n", #g0hyp);
    info *:= Sprintf("      %o not computed.\n", #g0hyp_notcomputed);
    info *:= Sprintf("      %o computed:\n", #g0hyp_computed);
    // info *:= Sprintf("        %o failed (non) lax sanity.\n", #g0hyp_failedsanity);
    info *:= Sprintf("        %o failed sanity.\n", #g0hyp_failedsanity);
  // g1
    // info *:= Sprintf("%o passport(s) of degree %o in BelyiDB/%o:\n", #f, d, d);
    assert #genus1 eq #g1hyp+#g1nonhyp;
    info *:= Sprintf("  %o genus 1:\n", #g1nonhyp+#g1hyp);
    info *:= Sprintf("    %o nonhyperbolic:\n", #g1nonhyp);
    info *:= Sprintf("      %o not computed.\n", #g1nonhyp_notcomputed);
    info *:= Sprintf("      %o computed:\n", #g1nonhyp_computed);
    // info *:= Sprintf("        %o failed lax sanity.\n", #g1nonhyp_failedlaxsanity);
    info *:= Sprintf("        %o failed sanity.\n", #g1nonhyp_failedlaxsanity);
    info *:= Sprintf("    %o hyperbolic:\n", #g1hyp);
    info *:= Sprintf("      %o not computed.\n", #g1hyp_notcomputed);
    info *:= Sprintf("      %o computed:\n", #g1hyp_computed);
    // info *:= Sprintf("        %o failed (non) lax sanity.\n", #g1hyp_failedsanity);
    info *:= Sprintf("        %o failed sanity.\n", #g1hyp_failedsanity);
  // g2
    // info *:= Sprintf("%o passport(s) of degree %o in BelyiDB/%o:\n", #f, d, d);
    assert #genus2 eq #g2hyp+#g2nonhyp;
    info *:= Sprintf("  %o genus 2:\n", #g2nonhyp+#g2hyp);
    info *:= Sprintf("    %o nonhyperbolic:\n", #g2nonhyp);
    info *:= Sprintf("      %o not computed.\n", #g2nonhyp_notcomputed);
    info *:= Sprintf("      %o computed:\n", #g2nonhyp_computed);
    // info *:= Sprintf("        %o failed lax sanity.\n", #g2nonhyp_failedlaxsanity);
    info *:= Sprintf("        %o failed sanity.\n", #g2nonhyp_failedlaxsanity);
    info *:= Sprintf("    %o hyperbolic:\n", #g2hyp);
    info *:= Sprintf("      %o not computed.\n", #g2hyp_notcomputed);
    info *:= Sprintf("      %o computed:\n", #g2hyp_computed);
    // info *:= Sprintf("        %o failed (non) lax sanity.\n", #g2hyp_failedsanity);
    info *:= Sprintf("        %o failed sanity.\n", #g2hyp_failedsanity);
  // g3
    // info *:= Sprintf("%o passport(s) of degree %o in BelyiDB/%o:\n", #f, d, d);
    assert #genus3 eq #g3hyp+#g3nonhyp;
    info *:= Sprintf("  %o genus 3:\n", #g3nonhyp+#g3hyp);
    info *:= Sprintf("    %o nonhyperbolic:\n", #g3nonhyp);
    info *:= Sprintf("      %o not computed.\n", #g3nonhyp_notcomputed);
    info *:= Sprintf("      %o computed:\n", #g3nonhyp_computed);
    // info *:= Sprintf("        %o failed lax sanity.\n", #g3nonhyp_failedlaxsanity);
    info *:= Sprintf("        %o failed sanity.\n", #g3nonhyp_failedlaxsanity);
    info *:= Sprintf("    %o hyperbolic:\n", #g3hyp);
    info *:= Sprintf("      %o not computed.\n", #g3hyp_notcomputed);
    info *:= Sprintf("      %o computed:\n", #g3hyp_computed);
    // info *:= Sprintf("        %o failed (non) lax sanity.\n", #g3hyp_failedsanity);
    info *:= Sprintf("        %o failed sanity.\n", #g3hyp_failedsanity);
  // gg
    // info *:= Sprintf("%o passport(s) of degree %o in BelyiDB/%o:\n", #f, d, d);
    assert #highergenus eq #gghyp+#ggnonhyp;
    info *:= Sprintf("  %o higher genus:\n", #ggnonhyp+#gghyp);
    info *:= Sprintf("    %o nonhyperbolic:\n", #ggnonhyp);
    info *:= Sprintf("      %o not computed.\n", #ggnonhyp_notcomputed);
    info *:= Sprintf("      %o computed:\n", #ggnonhyp_computed);
    // info *:= Sprintf("        %o failed lax sanity.\n", #ggnonhyp_failedlaxsanity);
    info *:= Sprintf("        %o failed sanity.\n", #ggnonhyp_failedlaxsanity);
    info *:= Sprintf("    %o hyperbolic:\n", #gghyp);
    info *:= Sprintf("      %o not computed.\n", #gghyp_notcomputed);
    info *:= Sprintf("      %o computed:\n", #gghyp_computed);
    // info *:= Sprintf("        %o failed (non) lax sanity.\n", #gghyp_failedsanity);
    info *:= Sprintf("        %o failed sanity.\n", #gghyp_failedsanity);
  // vprintf Shimura: "%o\n", info;
  if return_everything then
    print info;
    return g0nonhyp, g0nonhyp_notcomputed, g0nonhyp_computed, g0nonhyp_failedlaxsanity, g0hyp, g0hyp_notcomputed, g0hyp_computed, g0hyp_failedsanity, g1nonhyp, g1nonhyp_notcomputed, g1nonhyp_computed, g1nonhyp_failedlaxsanity, g1hyp, g1hyp_notcomputed, g1hyp_computed, g1hyp_failedsanity, g2nonhyp, g2nonhyp_notcomputed, g2nonhyp_computed, g2nonhyp_failedlaxsanity, g2hyp, g2hyp_notcomputed, g2hyp_computed, g2hyp_failedsanity, g3nonhyp, g3nonhyp_notcomputed, g3nonhyp_computed, g3nonhyp_failedlaxsanity, g3hyp, g3hyp_notcomputed, g3hyp_computed, g3hyp_failedsanity, ggnonhyp, ggnonhyp_notcomputed, ggnonhyp_computed, ggnonhyp_failedlaxsanity, gghyp, gghyp_notcomputed, gghyp_computed, gghyp_failedsanity;
    // return g0hyp_notcomputed, g0hyp_computed, g1hyp_notcomputed, g1hyp_computed, g2hyp_notcomputed, g2hyp_computed, g3hyp_notcomputed, g3hyp_computed, gghyp_notcomputed, gghyp_computed;
  else
    if return_hyp_notcomputed then
      print info;
      return g0hyp_notcomputed, g1hyp_notcomputed, g2hyp_notcomputed, g3hyp_notcomputed, gghyp_notcomputed;
    else
      return info;
    end if;
  end if;
end intrinsic;

intrinsic BelyiDBStatus(d::RngIntElt) -> Any
  {This assumes the current directory is /BelyiDB. Returns a string with information about BelyiMaps in /BelyiDB of degree d. This can easily be modified to give lots of information but for now is pretty minimal.}
  // directory stuff
  dir := GetCurrentDirectory();
  parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
  if parentdir eq "BelyiDB\n" then
    dbdirectory := dir;
  else
    error "make sure your working directory is /BelyiDB";
  end if;
  directory := dbdirectory cat Sprintf("/%o/", d);
  f := BelyiDBFilenames(d);
  info := "";
  genus0 := [];
  genus1 := [];
  genus2 := [];
  genus3 := [];
  highergenus := [];
  for i in {1..#f} do
    vprintf Shimura : "%o: (%o/%o)\n", f[i], i, #f;
    s := BelyiDBRead(f[i]);
    if s`BelyiDBGenus eq 0 then
      Append(~genus0, s);
    else
      if s`BelyiDBGenus eq 1 then
        Append(~genus1, s);
      else
        if s`BelyiDBGenus eq 2 then
          Append(~genus2, s);
        else
          if s`BelyiDBGenus eq 3 then
            Append(~genus3, s);
          else
            Append(~highergenus, s);
          end if;
        end if;
      end if;
    end if;
  end for;
  // g0
    g0nonhyp := [];
    g0nonhyp_notcomputed := [];
    g0nonhyp_computed := [];
    g0hyp := [];
    g0hyp_notcomputed := [];
    g0hyp_computed := [];
  // g1
    g1nonhyp := [];
    g1nonhyp_notcomputed := [];
    g1nonhyp_computed := [];
    g1hyp := [];
    g1hyp_notcomputed := [];
    g1hyp_computed := [];
  // g2
    g2nonhyp := [];
    g2nonhyp_notcomputed := [];
    g2nonhyp_computed := [];
    g2hyp := [];
    g2hyp_notcomputed := [];
    g2hyp_computed := [];
  // g3
    g3nonhyp := [];
    g3nonhyp_notcomputed := [];
    g3nonhyp_computed := [];
    g3hyp := [];
    g3hyp_notcomputed := [];
    g3hyp_computed := [];
  // gg
    ggnonhyp := [];
    ggnonhyp_notcomputed := [];
    ggnonhyp_computed := [];
    gghyp := [];
    gghyp_notcomputed := [];
    gghyp_computed := [];
  for i := 1 to #genus0 do
    s := genus0[i];
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~g0hyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~g0hyp_computed, s);
      else
        // hyperbolic and belyi maps not computed
        Append(~g0hyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~g0nonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~g0nonhyp_computed, s);
      else
        // nonhyperbolic and belyi maps not computed
        Append(~g0nonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  for i := 1 to #genus1 do
    s := genus1[i];
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~g1hyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~g1hyp_computed, s);
      else
        // hyperbolic and belyi maps not computed
        Append(~g1hyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~g1nonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~g1nonhyp_computed, s);
      else
        // nonhyperbolic and belyi maps not computed
        Append(~g1nonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  for i := 1 to #genus2 do
    s := genus2[i];
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~g2hyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~g2hyp_computed, s);
      else
        // hyperbolic and belyi maps not computed
        Append(~g2hyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~g2nonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~g2nonhyp_computed, s);
      else
        // nonhyperbolic and belyi maps not computed
        Append(~g2nonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  for i := 1 to #genus3 do
    s := genus3[i];
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~g3hyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~g3hyp_computed, s);
      else
        // hyperbolic and belyi maps not computed
        Append(~g3hyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~g3nonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~g3nonhyp_computed, s);
      else
        // nonhyperbolic and belyi maps not computed
        Append(~g3nonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  for i := 1 to #highergenus do
    s := highergenus[i];
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~gghyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~gghyp_computed, s);
      else
        // hyperbolic and belyi maps not computed
        Append(~gghyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~ggnonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~ggnonhyp_computed, s);
      else
        // nonhyperbolic and belyi maps not computed
        Append(~ggnonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  // g0
    assert #genus0 eq #g0hyp+#g0nonhyp;
    info *:= Sprintf("%o genus 0 hyperbolic:\n", #g0hyp);
    info *:= Sprintf("  %o not computed.\n", #g0hyp_notcomputed);
    info *:= Sprintf("  %o computed:\n", #g0hyp_computed);
  // g1
    assert #genus1 eq #g1hyp+#g1nonhyp;
    info *:= Sprintf("%o genus 1 hyperbolic:\n", #g1hyp);
    info *:= Sprintf("  %o not computed.\n", #g1hyp_notcomputed);
    info *:= Sprintf("  %o computed:\n", #g1hyp_computed);
  // g2
    assert #genus2 eq #g2hyp+#g2nonhyp;
    info *:= Sprintf("%o genus 2 hyperbolic:\n", #g2hyp);
    info *:= Sprintf("  %o not computed.\n", #g2hyp_notcomputed);
    info *:= Sprintf("  %o computed:\n", #g2hyp_computed);
  // g3
    assert #genus3 eq #g3hyp+#g3nonhyp;
    info *:= Sprintf("%o genus 3 hyperbolic:\n", #g3hyp);
    info *:= Sprintf("  %o not computed.\n", #g3hyp_notcomputed);
    info *:= Sprintf("  %o computed:\n", #g3hyp_computed);
  // gg
    assert #highergenus eq #gghyp+#ggnonhyp;
    info *:= Sprintf("%o higher genus hyperbolic:\n", #gghyp);
    info *:= Sprintf("  %o not computed.\n", #gghyp_notcomputed);
    info *:= Sprintf("  %o computed:\n", #gghyp_computed);
  // print and return
  print info;
  return g0hyp_notcomputed, g0hyp_computed, g1hyp_notcomputed, g1hyp_computed, g2hyp_notcomputed, g2hyp_computed, g3hyp_notcomputed, g3hyp_computed, gghyp_notcomputed, gghyp_computed;
end intrinsic;

intrinsic BelyiDBNonhyp(d::RngIntElt) -> Any
  {This assumes the current directory is /BelyiDB. Returns a string with information about BelyiMaps in /BelyiDB of degree d. This can easily be modified to give lots of information but for now is pretty minimal.}
  // directory stuff
  dir := GetCurrentDirectory();
  parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
  if parentdir eq "BelyiDB\n" then
    dbdirectory := dir;
  else
    error "make sure your working directory is /BelyiDB";
  end if;
  directory := dbdirectory cat Sprintf("/%o/", d);
  f := BelyiDBFilenames(d);
  info := "";
  genus0 := [];
  genus1 := [];
  genus2 := [];
  genus3 := [];
  highergenus := [];
  for i in {1..#f} do
    vprintf Shimura : "%o: (%o/%o)\n", f[i], i, #f;
    s := BelyiDBRead(f[i]);
    if s`BelyiDBGenus eq 0 then
      Append(~genus0, s);
    else
      if s`BelyiDBGenus eq 1 then
        Append(~genus1, s);
      else
        if s`BelyiDBGenus eq 2 then
          Append(~genus2, s);
        else
          if s`BelyiDBGenus eq 3 then
            Append(~genus3, s);
          else
            Append(~highergenus, s);
          end if;
        end if;
      end if;
    end if;
  end for;
  // g0
    g0nonhyp := [];
    g0nonhyp_notcomputed := [];
    g0nonhyp_computed := [];
    g0hyp := [];
    g0hyp_notcomputed := [];
    g0hyp_computed := [];
  // g1
    g1nonhyp := [];
    g1nonhyp_notcomputed := [];
    g1nonhyp_computed := [];
    g1hyp := [];
    g1hyp_notcomputed := [];
    g1hyp_computed := [];
  // g2
    g2nonhyp := [];
    g2nonhyp_notcomputed := [];
    g2nonhyp_computed := [];
    g2hyp := [];
    g2hyp_notcomputed := [];
    g2hyp_computed := [];
  // g3
    g3nonhyp := [];
    g3nonhyp_notcomputed := [];
    g3nonhyp_computed := [];
    g3hyp := [];
    g3hyp_notcomputed := [];
    g3hyp_computed := [];
  // gg
    ggnonhyp := [];
    ggnonhyp_notcomputed := [];
    ggnonhyp_computed := [];
    gghyp := [];
    gghyp_notcomputed := [];
    gghyp_computed := [];
  for i := 1 to #genus0 do
    s := genus0[i];
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~g0hyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~g0hyp_computed, s);
      else
        // hyperbolic and belyi maps not computed
        Append(~g0hyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~g0nonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~g0nonhyp_computed, s);
      else
        // nonhyperbolic and belyi maps not computed
        Append(~g0nonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  for i := 1 to #genus1 do
    s := genus1[i];
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~g1hyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~g1hyp_computed, s);
      else
        // hyperbolic and belyi maps not computed
        Append(~g1hyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~g1nonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~g1nonhyp_computed, s);
      else
        // nonhyperbolic and belyi maps not computed
        Append(~g1nonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  for i := 1 to #genus2 do
    s := genus2[i];
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~g2hyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~g2hyp_computed, s);
      else
        // hyperbolic and belyi maps not computed
        Append(~g2hyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~g2nonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~g2nonhyp_computed, s);
      else
        // nonhyperbolic and belyi maps not computed
        Append(~g2nonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  for i := 1 to #genus3 do
    s := genus3[i];
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~g3hyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~g3hyp_computed, s);
      else
        // hyperbolic and belyi maps not computed
        Append(~g3hyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~g3nonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~g3nonhyp_computed, s);
      else
        // nonhyperbolic and belyi maps not computed
        Append(~g3nonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  for i := 1 to #highergenus do
    s := highergenus[i];
    if s`BelyiDBType eq "Hyperbolic" then
      // hyperbolic
      Append(~gghyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // hyperbolic and belyi maps computed
        Append(~gghyp_computed, s);
      else
        // hyperbolic and belyi maps not computed
        Append(~gghyp_notcomputed, s);
      end if;
    else
      // nonhyperbolic
      Append(~ggnonhyp, s);
      if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
        // nonhyperbolic and belyi maps computed
        Append(~ggnonhyp_computed, s);
      else
        // nonhyperbolic and belyi maps not computed
        Append(~ggnonhyp_notcomputed, s);
      end if;
    end if;
  end for;
  // g0
    assert #genus0 eq #g0hyp+#g0nonhyp;
    info *:= Sprintf("%o genus 0 nonhyperbolic:\n", #g0nonhyp);
    info *:= Sprintf("  %o not computed.\n", #g0nonhyp_notcomputed);
    info *:= Sprintf("  %o computed:\n", #g0nonhyp_computed);
  // g1
    assert #genus1 eq #g1hyp+#g1nonhyp;
    info *:= Sprintf("%o genus 1 nonhyperbolic:\n", #g1nonhyp);
    info *:= Sprintf("  %o not computed.\n", #g1nonhyp_notcomputed);
    info *:= Sprintf("  %o computed:\n", #g1nonhyp_computed);
  // g2
    assert #genus2 eq #g2hyp+#g2nonhyp;
    info *:= Sprintf("%o genus 2 nonhyperbolic:\n", #g2nonhyp);
    info *:= Sprintf("  %o not computed.\n", #g2nonhyp_notcomputed);
    info *:= Sprintf("  %o computed:\n", #g2nonhyp_computed);
  // g3
    assert #genus3 eq #g3hyp+#g3nonhyp;
    info *:= Sprintf("%o genus 3 nonhyperbolic:\n", #g3nonhyp);
    info *:= Sprintf("  %o not computed.\n", #g3nonhyp_notcomputed);
    info *:= Sprintf("  %o computed:\n", #g3nonhyp_computed);
  // gg
    assert #highergenus eq #gghyp+#ggnonhyp;
    info *:= Sprintf("%o higher genus nonhyperbolic:\n", #ggnonhyp);
    info *:= Sprintf("  %o not computed.\n", #ggnonhyp_notcomputed);
    info *:= Sprintf("  %o computed:\n", #ggnonhyp_computed);
  // print and return
  print info;
  return g0nonhyp_notcomputed, g0nonhyp_computed, g1nonhyp_notcomputed, g1nonhyp_computed, g2nonhyp_notcomputed, g2nonhyp_computed, g3nonhyp_notcomputed, g3nonhyp_computed, ggnonhyp_notcomputed, ggnonhyp_computed;
end intrinsic;
