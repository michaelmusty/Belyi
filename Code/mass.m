// Main feature suggestion: if there is non-zero mass for a subgroup, we may want to indicate that. To be discussed.
// Other: Splitting of bigger conjugacy classes

declare attributes GrpPerm: CharacterTables;

intrinsic CalculateCharacterTable(G::GrpPerm, S::GrpPerm) -> SeqEnum, SeqEnum, GrpPermElt
    {Finds the character table and conjugacy classes of the subgroup G of the group S, using a stored value if possible. In the latter case an element conjugating G to the stored group is also returned.}
    // Initialize table for lookup if that has not been created yet:
    if not assigned S`CharacterTables then
        S`CharacterTables := [ ];
    end if;
    // Use a stored value if possible:
    for tup in S`CharacterTables do
        test, s := IsConjugate(S, G, tup[1]);
        if test then
            X := tup[3];
            // Conjugate stored representative to obtain representative in the
            // original group:
            Cs := [ < C[1], C[2], C[3]^(s^(-1)) > : C in tup[2] ];
            return X, Cs, s;
        end if;
    end for;
    // Otherwise add a new entry:
    X := CharacterTable(G);
    Cs := [ < x : x in tup > : tup in ConjugacyClasses(G) ];
    S`CharacterTables cat:= [ [* G, Cs, X *] ];
    return X, Cs, Identity(S);
end intrinsic;

intrinsic SplitClass(C::Tup, H::GrpPerm, G::GrpPerm, S::GrpPerm) -> SeqEnum
    {Splits a conjugacy class C of G into conjugacy classes of the subgroup H.}
    // This is a stupid algorithm, but permissible in our specific
    // circumstances, since we will need the result of the character table
    // calculation later anyway.
    X, CHs, s := CalculateCharacterTable(H, S);
    return [ CH : CH in CHs | IsConjugate(G, C[3], CH[3]) ];
end intrinsic;

intrinsic SerreCount(Cs::SeqEnum[Tup], G::GrpPerm, S::GrpPerm) -> RngIntElt
    {Finds total number of dessins with passport contained in (G, Cs).}
    // Serre's classical formula:
    X, CGs, g := CalculateCharacterTable(G, S);
    m := &+[ &*[ x(C[3]^g) : C in Cs ]/x(Identity(G))^(#Cs - 2) : x in X ];
    m *:= &*[ C[2] : C in Cs ];
    m /:= #G;
    return m;
end intrinsic;

intrinsic SerreCountForSubgroup(Cs::SeqEnum[Tup], H::GrpPerm, G::GrpPerm, S::GrpPerm) -> RngIntElt
    {Finds total number of dessins with passport (G, Cs) whose monodromy group is contained in H < G.}
    CP := [ SplitClass(C, H, G, S) : C in Cs ];
    counts := [ SerreCount([ CsH : CsH in tup ], H, S) : tup in CartesianProduct(CP) ];
    // Magma does not accept empty sums, so we have to get around this:
    if #counts eq 0 then
        return 0;
    end if;
    return &+(counts);
end intrinsic;

intrinsic MaximalSubgroupsUpToAmbientConjugation(H::GrpPerm, G::GrpPerm) -> SeqEnum
    {Finds the maximal subgroups of H up to conjugation by the ambient group G.}
    Ks := [ rec`subgroup : rec in MaximalSubgroups(H) ];
    return [ Ks[i] : i in [1..#Ks] | &and([ not IsConjugate(G, Ks[i], Ks[j]) : j in [1..i-1] ]) ];
end intrinsic;

intrinsic SerreCountLattice(Cs::SeqEnum[Tup], G::GrpPerm, S::GrpPerm : depth := 1) -> SeqEnum
    {Finds part of the lattice of subgroups in which solutions in the given conjugacy classes exist.}
    Lat := [ [* G, SerreCount(Cs, G, S), [ ] *] ];
    if depth eq 0 then
        return Lat;
    end if;
    KsMax0 := [ rec`subgroup : rec in MaximalSubgroups(G) ];
    KsMax := [ ];
    i := 0;
    for K in KsMax0 do
        count := SerreCountForSubgroup(Cs, K, G, S);
        // We do not care about subgroups with contribution 0:
        if count ne 0 then
            i +:= 1;
            Append(~KsMax, K);
            Append(~Lat, [* K, count, [ i ] *]);
        end if;
    end for;
    TestGpsCont := KsMax;
    current_depth := 1;
    // Keep adding maximal subgroups that could potentially lead to solutions
    // until the specified depth is exceeded:
    while (not IsEmpty(TestGpsCont)) and (current_depth lt depth) do
        TestGps := &cat[ MaximalSubgroupsUpToAmbientConjugation(K, G) : K in TestGpsCont ];
        TestGpsCont := [ ];
        for K in TestGps do
            count := SerreCountForSubgroup(Cs, K, G, S);
            isnew := not &or[ IsConjugate(G, K, tup[1]) : tup in Lat ];
            if (count ne 0) and isnew then
                indices := [ i : i in [1..#KsMax] | IsConjugateSubgroup(G, KsMax[i], K) ];
                Append(~Lat, [* K, count, indices *]);
                // We stop once we are in full intersection since we care only
                // about maximal subgroups in the end:
                if not #indices eq #KsMax then
                    Append(~TestGpsCont, K);
                end if;
            end if;
        end for;
        current_depth +:= 1;
    end while;
    return Lat;
end intrinsic;

intrinsic MaximalSerreCountLattice(Cs::SeqEnum[Tup], G::GrpPerm, S::GrpPerm : depth := 1) -> SeqEnum
    {Refines a SerreCountLattice so that only maximal elements in the same intersections up to conjugation by G are returned.}
    // Creating non-refined lattice:
    Lat := SerreCountLattice(Cs, G, S : depth := depth);
    n := #Lat;
    if n eq 0 then
        return [ ];
    end if;
    // Removing entries with same intersection property that are G-conjugate to subgroups of others:
    remove := { };
    for i:=1 to n do
        for j:=i+1 to n do
            if Lat[i][3] eq Lat[j][3] then
                if IsConjugateSubgroup(G, Lat[i][1], Lat[j][1]) then
                    Include(~remove, j);
                else
                    if IsConjugateSubgroup(G, Lat[j][1], Lat[i][1]) then
                        Include(~remove, i);
                    end if;
                end if;
            end if;
        end for;
    end for;
    Lat := [ Lat[i] : i in {1..n} diff remove ];
    // Sorting (roughly from large to small) for inclusion-exclusion later:
    N := Max([ #tup[3] : tup in Lat ]);
    Lat := &cat([ [ tup : tup in Lat | #tup[3] eq i ] : i in [0..N] ]);
    return Lat;
end intrinsic;

intrinsic CountEstimate(Cs::SeqEnum[Tup], G::GrpPerm, S::GrpPerm : depth := 1) -> RngIntElt
    {Estimates the total number of dessins with passport (G, Cs) up to conjugation by ambient S.}
    Lat := MaximalSerreCountLattice(Cs, G, S : depth := depth);
    // To deal with empty set:
    meets_done := Exclude({{1}}, {1});
    n := 0;
    for tup in Lat do
        index := Index(G, Normalizer(G, tup[1]));
        // Alternative line that (mysteriously) works better in practice:
        //index := Index(G, tup[1])/#Center(G);
        meet_tup := tup[3];
        mult1 := #[ tup1 : tup1 in Lat | tup1[3] eq meet_tup ];
        // Finding all intersections in which the indicated group appears:
        mult2 := 0;
        // Problem with empty set:
        for sub in Subsets(Set(meet_tup)) do
            if not sub in meets_done then
                mult2 +:= (-1)^(#sub);
                Include(~meets_done, sub);
            end if;
        end for;
        // Weighing to obtain good estimate for conjugates:
        n +:= index * mult1 * mult2 * tup[2];
    end for;
    return n;
end intrinsic;

intrinsic DessinEstimate(Cs::SeqEnum[Tup], G::GrpPerm, S::GrpPerm : depth := 1) -> FldRatElt
    {Estimates the total number of dessins up to isomorphism with passport (G, Cs) up to conjugation by ambient S.}
    // TODO: Slight amount of doubt left.
    // What follows is not clever, but the alternative is to create the G-set
    // of conjugacy classes. It may also be better not to use &and.
    // Normalizer of the full group
    N1 := Normalizer(S, G);
    reps := DoubleCosetRepresentatives(N1, G, sub<N1 | 1>);
    // Representatives of those elements that also stabilize the classes:
    N2RepsModG := [ rep : rep in reps | &and[ IsConjugate(G, C[3], C[3]^rep) : C in Cs ] ];
    // Automorphism group cardinality for all dessins in question:
    Z := Centralizer(S, G);
    factor := #Z / (#N2RepsModG * #G);
    if depth eq 1 then
        est := factor * CountEstimate(Cs, G, S : depth := depth);
        est0 := factor * CountEstimate(Cs, G, S : depth := 0);
        int := [ Ceiling(est)..Floor(est0) ];
        int := [ n : n in int | n ge 0 ];
        return est, #int eq 1;
    end if;
    return  factor * CountEstimate(Cs, G, S : depth := depth);
end intrinsic;

intrinsic DessinEstimate(Cs::SeqEnum[GrpPermElt], G::GrpPerm, S::GrpPerm : depth := 1) -> FldRatElt
    {Estimates the total number of dessins up to isomorphism with passport (G, Cs) up to conjugation by ambient S.}
    X, CGs, s := CalculateCharacterTable(G, S);
    CCs := &cat[ [ CG : CG in CGs | IsConjugate(G, CG[3], C) ] : C in Cs ];
    return DessinEstimate(CCs, G, S : depth := depth);
end intrinsic;

intrinsic CountEstimateNaive(CReps::SeqEnum[GrpPermElt], H::GrpPerm, G::GrpPerm) -> RngIntElt
    {bla.}
    n := 0;
    for h0 in Conjugates(H, CReps[1]) do
        for h1 in Conjugates(H, CReps[2]) do
            hi := (h0 * h1)^(-1);
            if IsConjugate(H, hi, CReps[3]) and sub<H | [h0, h1]> eq H then
                n +:= 1;
            end if;
        end for;
    end for;
    return n;
end intrinsic;

intrinsic CountEstimateNaive(CReps::SeqEnum[Tup], H::GrpPerm, G::GrpPerm) -> RngIntElt
    {bla.}
    return CountEstimateNaive([ CRep[3] : CRep in CReps ], H, G);
end intrinsic;
