declare type BelyiDB;
declare attributes BelyiDB:
// easy attrs
  BelyiDBName,
  BelyiDBFilename,
  BelyiDBDegree,
  BelyiDBOrders, // formerly known as ABC
  BelyiDBType, // Hyperbolic, Euclidean, or Spherical
  BelyiDBGenus,
  BelyiDBSize,
  BelyiDBPointedSize,
// permutation attrs
  BelyiDBPermutationTriple,
  BelyiDBMonodromyGroup,
  BelyiDBAutomorphismGroup,
  BelyiDBPointedAutomorphismGroup,
  BelyiDBPassport,
  BelyiDBPointedPassport,
  BelyiDBGaloisOrbits,
// field attrs
  BelyiDBBaseFieldData, // [* [* K, Kv, conj, complex embeddding *],... *]
// belyimap attrs
  BelyiDBBelyiCurves,
  BelyiDBBelyiMaps,
// exact attrs
  BelyiDBExactCurveInvariants,
  BelyiDBExactCurveCoefficients,
  BelyiDBExactBelyiMapLeadingCoefficients,
  BelyiDBExactBelyiMapNumeratorCoefficients,
  BelyiDBExactBelyiMapDenominatorCoefficients,
// numerical attrs
  BelyiDBRescalingFactors, // list of complex numbers
  BelyiDBPowserIndat, // how bout dat indat
  BelyiDBPowserBases; // fout_ech in Gamma`TrianglePowserBases = [* indat, [* fout_ech, minsing, fout *] *]

intrinsic BelyiDBInitialize() -> BelyiDB
  {Create an empty BelyiDB object.}
  s := New(BelyiDB);
  return s;
end intrinsic;

intrinsic BelyiDBCopy(s::BelyiDB) -> BelyiDB
  {new instance of BelyiDB.}
  s1 := BelyiDBInitialize();
  for attr in GetAttributes(Type(s)) do
    if assigned s``attr then
      s1``attr := s``attr;
    end if;
  end for;
  return s1;
end intrinsic;

intrinsic Print(s::BelyiDB)
  {Print BelyiDB}
  printf "BelyiDB %o:\n", s`BelyiDBName;
  printf "  Degree %o\n", s`BelyiDBDegree;
  printf "  Genus %o\n", s`BelyiDBGenus;
  printf "  %o\n", s`BelyiDBType;
  printf "  Size %o\n", s`BelyiDBSize;
  printf "  PointedSize %o\n", s`BelyiDBPointedSize;
  if assigned s`BelyiDBGaloisOrbits then
    printf "  #GaloisOrbits = %o\n", #s`BelyiDBGaloisOrbits;
  end if;
  if assigned s`BelyiDBBelyiCurves and assigned s`BelyiDBBelyiMaps then
    if #s`BelyiDBBelyiCurves eq #s`BelyiDBPointedPassport and #s`BelyiDBBelyiMaps eq #s`BelyiDBPointedPassport then
      printf "  BelyiMaps computed :)\n";
    else
      printf "  BelyiMaps assigned but numbers don't match up! Check this BelyiDBObject!\n";
    end if;
  else
    printf "  BelyiMaps NOT computed :(\n";
  end if;
end intrinsic;

/*
  // TODO make equality take precision into account?
  intrinsic 'eq'(s::BelyiDBObject, t::BelyiDBObject) -> BoolElt
    {Return whether s is equal to t.}
    for attr in GetAttributes(Type(s)) do
      if assigned s``attr then
        if assigned t``attr then
          if Type(s``attr) ne Type(t``attr) then
            return false;
          elif s``attr ne t``attr then
            return false;
          end if;
        else
          return false;
        end if;
      else
        if assigned t``attr then
          return false;
        end if;
      end if;
    end for;
    return true;
  end intrinsic;
*/
