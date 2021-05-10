intrinsic AutomorphismGroup(sigma::SeqEnum[GrpPermElt]) -> GrpPerm
    {Returns the automorphism group of the dessin.}
    S := Generic(Parent(sigma[1]));
    G := sub<S|sigma>;
    sigma := [G!sigma[i] : i in [1..3]];
    return &meet[ Centralizer(S, s) : s in sigma ];
end intrinsic;

intrinsic PointedAutomorphismGroup(sigma::SeqEnum[GrpPermElt] : bp := 1, sh := 1) -> GrpPerm
    {Returns the automorphism group of the dessin, pointed by the sheet 1 above
    the first branch point.}
    G := AutomorphismGroup(sigma);
    cycles := CycleDecomposition(sigma[bp]);
    gset := GSet(G, Set(cycles));
    cycle := [ cycle : cycle in cycles | sh in cycle ][1];
    return Stabilizer(G, gset ! cycle);
end intrinsic;

intrinsic WishlistCase1(d::RngIntElt : just_names := false) -> Any
  {returns a list of pairs [* s, sigma *] where s is a BelyiDB object and AutomorphismGroup(sigma) gt PointedAutomorphismGroup(sigma) gt 1.}
  // directory stuff
  dir := GetCurrentDirectory();
  parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
  if parentdir eq "BelyiDB\n" then
    dbdirectory := dir;
  else
    error "make sure your working directory is /BelyiDB";
  end if;
  case1 := [* *];
  f := BelyiDBFilenames(d);
  for i := 1 to #f do
    vprintf Shimura : "d=%o, i=%o/%o:\n", d, i, #f;
    s := BelyiDBRead(f[i]);
    ppass := s`BelyiDBPointedPassport;
    for sigma in ppass do
      auto := AutomorphismGroup(sigma);
      pauto := PointedAutomorphismGroup(sigma);
      if (#pauto gt 1) and (#auto gt #pauto) then
        if just_names then
          Append(~case1, [* s`BelyiDBName, sigma *]);
        else
          Append(~case1, [* s, sigma *]);
        end if;
      end if;
    end for;
  end for;
  return case1;
end intrinsic;

intrinsic WishlistCase2(d::RngIntElt : just_names := false) -> Any
  {returns a list of pairs [* s, sigma *] where s is a BelyiDB object and AutomorphismGroup(sigma) gt 1.}
  // directory stuff
  dir := GetCurrentDirectory();
  parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
  if parentdir eq "BelyiDB\n" then
    dbdirectory := dir;
  else
    error "make sure your working directory is /BelyiDB";
  end if;
  case2 := [* *];
  f := BelyiDBFilenames(d);
  for i := 1 to #f do
    vprintf Shimura : "d=%o, i=%o/%o:\n", d, i, #f;
    s := BelyiDBRead(f[i]);
    ppass := s`BelyiDBPointedPassport;
    for sigma in ppass do
      auto := AutomorphismGroup(sigma);
      pauto := PointedAutomorphismGroup(sigma);
      if #auto gt 1 then
        if just_names then
          Append(~case2, [* s`BelyiDBName, sigma *]);
        else
          Append(~case2, [* s, sigma *]);
        end if;
      end if;
    end for;
  end for;
  return case2;
end intrinsic;
