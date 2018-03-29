declare verbose Passport, 1;

declare attributes GrpPerm: ClassesModAmbients;
declare attributes GrpPerm: NormalizerInAmbient;

 /* Auxiliary functions: */

intrinsic NormalizerInAmbient(G::GrpPerm) -> GrpPerm
    {Returns the normalizer of a permutation group in the symmetric group on
    its letters.}
    if assigned G`NormalizerInAmbient then
        return G`NormalizerInAmbient;
    end if;
    N := Normalizer(SymmetricGroup(Degree(G)), G);
    G`NormalizerInAmbient := N;
    return N;
end intrinsic;

intrinsic ConjugacyClass(G::GrpPerm, g::GrpPermElt) -> Tup
    {Returns the conjugacy class data for g as an element of G.}
    // NOTE: the following line is a lookup once it has been calculated before,
    // so no time is lost here. The same holds for later invocations.
    CCG := ConjugacyClasses(G);
    for CC in CCG do
        if IsConjugate(G, g, CC[3]) then
            return CC;
        end if;
    end for;
end intrinsic;

/* Conjugacy classes modulo ambient: */

intrinsic ConjugacyClassesModAmbient(G::GrpPerm, N::GrpPerm) -> SeqEnum[Tup]
    {Returns conjugacy classes representatives of G up to the conjugation action
    of N, where G is a subgroup of N.}
    ass := assigned G`ClassesModAmbients;
    test := false;
    // If data has been stored, then lookup and return if it is in there
    if ass then
        test := N in [ class[1] : class in G`ClassesModAmbients ];
    end if;
    if test then
        return [ class[2] : class in G`ClassesModAmbients | class[1] eq N ][1];
    end if;

    CCG := ConjugacyClasses(G);
    if N eq G then
        CCGModN := [ tup : tup in CCG ];
    else
        CCGModN := [];
        for i in [1..#CCG] do
            done := false;
            for j in [1..#CCGModN] do
                // If we find a duplicate, merge the classes
                // (and add cardinalities)
                if IsConjugate(N, CCG[i][3], CCGModN[j][3]) then
                    CCGModN[j][2] +:= CCG[i][2];
                    done := true;
                    break;
                end if;
            end for;
            if not done then
                Append(~CCGModN, CCG[i]);
            end if;
        end for;
    end if;

    // Initialize data structure if needed
    if not ass then
        G`ClassesModAmbients := [];
    end if;
    // Store result
    G`ClassesModAmbients cat:= [ [* N, CCGModN *] ];
    return CCGModN;
end intrinsic;

intrinsic ClassRepresentativesModAmbient(G::GrpPerm, N::GrpPerm) -> SeqEnum
    {Returns conjugacy class representatives of G up to the conjugation action
    of N, where G is a subgroup of N.}
    return [ class[3] : class in ConjugacyClassesModAmbient(G, N) ];
end intrinsic;

intrinsic ConjugacyClassModAmbient(G::GrpPerm, N::GrpPerm, g::GrpPermElt) -> Tup
    {Returns the conjugacy class data for g as an element of G, modulo ambient N.}
    CCGModN := ConjugacyClassesModAmbient(G, N);
    for CC in CCGModN do
        if IsConjugate(N, g, CC[3]) then
            return CC;
        end if;
    end for;
end intrinsic;

/* Some primitive lookups: */

intrinsic ConjugacyClassNumber(G::GrpPerm, g::GrpPermElt) -> Tup
    {Returns the conjugacy class number for g in the set of conjugacy classes
    of G. Note that this output is inconsistent, but not after the classes have
    been calculated once.}
    CCG := ConjugacyClasses(G);
    for i:=1 to #CCG do
        if IsConjugate(G, g, CCG[i][3]) then
            return i;
        end if;
    end for;
end intrinsic;

intrinsic ConjugacyClassNumber(G::GrpPerm, C::Tup) -> Tup
    {Returns the conjugacy class number for C in the set of conjugacy classes
    of G. Note that this output is inconsistent, but not after the classes have
    been calculated once.}
    return ConjugacyClassNumber(G, C[3]);
end intrinsic;

intrinsic ConjugacyClassModAmbientNumber(G::GrpPerm, N::GrpPerm, g::GrpElt) -> Tup
    {Returns the conjugacy class number for g in the set of conjugacy classes
    of G, up to the ambient N. Note that this output is inconsistent, but not
    after the classes have been calculated once.}
    CCGModN := ConjugacyClassesModAmbient(G, N);
    for i:=1 to #CCGModN do
        if IsConjugate(N, g, CCGModN[i][3]) then
            return i;
        end if;
    end for;
end intrinsic;

intrinsic ConjugacyClassModAmbientNumber(G::GrpPerm, N::GrpPerm, C::Tup) -> Tup
    {Returns the conjugacy class number for C in the set of conjugacy classes
    of G, up to the ambient N. Note that this output is inconsistent, but not
    after the classes have been calculated once.}
    CCGModN := ConjugacyClassesModAmbient(G, N);
    for i:=1 to #CCGModN do
        if IsConjugate(N, C[3], CCGModN[i][3]) then
            return i;
        end if;
    end for;
end intrinsic;

/* Weak equivalence: */

intrinsic S3Action(g::GrpPermElt, sigma::SeqEnum[GrpPermElt]) -> SeqEnum[GrpPermElt]
    {Transforms a Belyi map sigma by the left action of an element g of
    Sym(3).}
    sigmap := [ sigma[i^g] : i in [1..#sigma] ];
    if IsOdd(g) then
        sigmap := [ s^(-1) : s in sigmap ];
    end if;
    return sigmap;
end intrinsic;

intrinsic S3Action(g::GrpPermElt, CCs::SeqEnum[Tup]) -> SeqEnum[Tup]
    {Transforms a triple of conjugacy classes CCs by the left action of an
    element g of Sym(3).}
    G := Parent(CCs[1][3]);
    CCG := ConjugacyClasses(G);
    if IsEven(g) then
        return [ CCs[i^g] : i in [1..#CCs] ];
    else
        return [ ConjugacyClass(G, CCs[i^g][3]^(-1)) : i in [1..#CCs] ];
    end if;
end intrinsic;

intrinsic S3Action(g::GrpPermElt, cycstrs::SeqEnum[SeqEnum[Tup]]) -> SeqEnum[SeqEnum[Tup]]
    {Transforms a triple of cycle structures cycstrs by the left action of an
    element g of Sym(3).}
    return [ cycstrs[i^g] : i in [1..#cycstrs] ];
end intrinsic;

intrinsic S3Action(g::GrpPermElt, inds::SeqEnum[RngIntElt], G::GrpPerm, N::GrpPerm) -> SeqEnum[RngIntElt]
    {Transforms a triple of conjugacy classes indices inds by the left action of an
    element g of Sym(3).}
    CCG := ConjugacyClassesModAmbient(G, N);
    if IsEven(g) then
        return [ inds[i^g] : i in [1..#inds] ];
    else
        return [ ConjugacyClassModAmbientNumber(G, N, CCG[inds[i^g]][3]^(-1)) : i in [1..#inds] ];
    end if;
end intrinsic;

intrinsic IsWeaklyIsomorphic(N::GrpPerm, sigma::SeqEnum[GrpPermElt], tau::SeqEnum[GrpPermElt]) -> BoolElt
    {Determines if two dessins sigma and tau are weakly isomorphic. These are
    supposed to generate the same monodromy group; N is a group containing this
    monodromy group that functions as an ambient.}
    // We could make the group over which we run smaller, but in practice this
    // is not a big deal, and it does not seem very efficient.
    //gs := [ ];
    //for g in Sym(3) do
    //    sigmap := [ sigma[i^g] : i in [1..#sigma] ];
    //    if IsOdd(g) then
    //        sigmap := [ s^(-1) : s in sigmap ];
    //    end if;
    //    if &and[ IsConjugate(N, sigmap[i], tau[i]) : i in [1..3] ] then
    //        Append(~gs, g);
    //    end if;
    //end for;
    for g in Sym(3) do
        if IsConjugate(N, S3Action(g, sigma), tau) then
            return true;
        end if;
    end for;
    return false;
end intrinsic;

/* Representatives of conjugacy classes up to weak equivalence: */

intrinsic IsInCanonicalOrderC3(inds::SeqEnum[RngIntElt]) -> BoolElt
    {Determines if a triple of integers is ordered well with respect to
    rotation of the indices.}
    // TODO: There is perhaps room to play here in order to reduce running time
    // Current choice: equality or (a, b, c) with a <= b and a < c.
    return ((inds[1] eq inds[2]) and (inds[1] eq inds[3])) or ((inds[1] le inds[2]) and (inds[1] lt inds[3]));
end intrinsic;

intrinsic CanonicalOrderC3(inds::SeqEnum[RngIntElt]) -> SeqEnum[RngIntElt]
    {Canonically orders a triple of integers with respect to rotation of the
    indices.}
    g0 := Sym(3) ! (1,2,3);
    for e:=0 to 2 do
        g := g0^e;
        indsnew := [ inds[i^g] : i in [1..#inds] ];
        if IsInCanonicalOrderC3(indsnew) then
            return indsnew;
        end if;;
    end for;
end intrinsic;

intrinsic S3Representatives(tups::SeqEnum[SeqEnum[RngIntElt]], G::GrpPerm, N::GrpPerm) -> SeqEnum[SeqEnum[RngIntElt]]
    {Given a set of triples of conjugacy classes, presumed stable under the
    action of Sym(3), determines a set of representatives under this action.
    Uses group G and ambient N. Uses a labeling.}
    CCGModN := ConjugacyClassesModAmbient(G, N);
    indss := tups;
    indss := [ inds : inds in indss | IsInCanonicalOrderC3(inds) ];
    if &and[ &and[ IsConjugate(N, CCGModN[ind][3], CCGModN[ind][3]^(-1)) : ind in inds ] : inds in indss ] then
        indss := [ inds : inds in indss | inds[2] le inds[3] ];
    else
        // If we cannot use the above then we just apply some element of order
        // 2 and order the result cyclically to see which one is better.
        S2 := sub<Sym(3) | (1,2)>;
        indssxS2 := CartesianProduct(Set(indss), S2);
        // Note that we do get a right action here because the group has order 2:
        f := map< indssxS2 -> Set(indss) | tup :-> CanonicalOrderC3(S3Action(tup[2], tup[1], G, N)) >;
        indssGSet := GSet(S2, Set(indss), f);
        // Pick out one with a large conjugacy class as first element:
        indss := [ Sort([ elt : elt in Set(orbit) ], func<L1,L2 | L2[1] - L1[1]>)[1] : orbit in Orbits(S2, indssGSet) ];
    end if;
    return indss;
end intrinsic;

intrinsic S3Representatives(tups::SeqEnum[SeqEnum[Tup]], G::GrpPerm, N::GrpPerm) -> SeqEnum[SeqEnum[Tup]]
    {Given a set of triples of conjugacy classes, presumed stable under the
    action of Sym(3), determines a set of representatives under this action.
    Uses group G and ambient N.}
    CCGModN := ConjugacyClassesModAmbient(G, N);
    indss := [ [ ConjugacyClassModAmbientNumber(G, N, CC) : CC in tup ] : tup in tups ];
    indss := [ inds : inds in indss | IsInCanonicalOrderC3(inds) ];
    if &and[ &and[ IsConjugate(N, CC[3], CC[3]^(-1)) : CC in tup ] : tup in tups ] then
        indss := [ inds : inds in indss | inds[2] le inds[3] ];
    else
        // Like the previous function
        S2 := sub<Sym(3) | (1,2)>;
        indssxS2 := CartesianProduct(Set(indss), S2);
        f := map< indssxS2 -> Set(indss) | tup :-> CanonicalOrderC3(S3Action(tup[2], tup[1], G, N)) >;
        r := Random(indss);
        indssGSet := GSet(S2, Set(indss), f);
        indss := [ Representative(Set(orbit)) : orbit in Orbits(S2, indssGSet) ];
    end if;
    return [ [ CCGModN[ind] : ind in inds ] : inds in indss ];
end intrinsic;

// In the big function, a much simpler version suffices; since we only use
// cycle types, we can sort directly.
intrinsic S3Representatives(tups::SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[SeqEnum[RngIntElt]]
    {Returns tuples that are in order.}
    return [ tup : tup in Set([ Sort(tup) : tup in tups ]) ];
end intrinsic;

intrinsic S3Representative(tup::SeqEnum[RngIntElt]) -> SeqEnum[RngIntElt]
    {Orders a tuple.}
    return Sort(tup);
end intrinsic;

/* Passport lemma (fundamental): */

intrinsic PassportLemma(G::GrpPerm, tau::SeqEnum[GrpPermElt] : generates := true) -> SeqEnum
    {Given a transitive permutation group G, and representatives tau of two
    conjugacy classes in N := Normalizer(S, G), return double coset reps for
    Centralizer(N, tau[1])\N/Centralizer(N, tau[2]).
    Setting generates to true will select only those representatives for which
    the corresponding dessin has monodromy group G (and not merely contained in
    G.}
    N := NormalizerInAmbient(G);
    S := SymmetricGroup(Degree(G));
    nus := DoubleCosetRepresentatives(N, Centralizer(N, tau[1]), Centralizer(N, tau[2]));
    pairs := [ [ G ! tau[1], G ! (nu*tau[2]*nu^(-1)) ] : nu in nus ];
    if generates then
        pairs := [ pair : pair in pairs | sub< S | pair > eq G ];
    end if;
    return pairs;
end intrinsic;

/* Distilling pointed refinements: */

intrinsic CyclesOverBasePoint(sigma::SeqEnum, bp::RngIntElt, ln::RngIntElt, aut::RngIntElt) -> SeqEnum
    {Given a permutation triple sigma computes the cycles of length ln in
    sigma[bp] up to simultaneous conjugation in Sym(d).  Here bp specifies in
    which permutation we mark a cycle, i.e., bp := 1,2,3 corresponds to sigma0,
    sigma1, sigmaoo (default is sigma0).}
    cycles := CycleDecomposition(sigma[bp]);
    cycles := { cycle : cycle in cycles | #cycle eq ln };
    /* Generic cases get fast result */
    if #cycles eq 0 then
        return [ ];
    elif #cycles eq 1 then
        return [ Set(cyc) : cyc in cycles ];
    end if;

    /* Otherwise we take distinguished points and automorphisms into account */
    cycles := { cycle : cycle in cycles | #PointedAutomorphismGroup(sigma : bp := bp, sh := cycle[1]) eq aut };
    S := Sym(Degree(Parent(sigma[1])));
    G := sub<S | [ S ! s : s in sigma]>;
    C := Centralizer(S, G);
    gset := GSet(C, cycles); orbits := Orbits(C, gset);
    return [ Set(orbit[1]) : orbit in orbits ];
end intrinsic;

intrinsic PointedRefinementSetFromCycles(sigma::SeqEnum, bp::RngIntElt, cycs::SeqEnum) -> SeqEnum
    {Normalizes the pointed refinements over the base point bp corresponding to
    the cycles in cycs.}
    S := Sym(Degree(Parent(sigma[1])));
    G := sub<S | [ S ! s : s in sigma]>;
    gset := GSet(G, {1..Degree(G)});
    sigma_ref := [ ];
    for cyc in cycs do
        x := [ s : s in cyc ][1];
        test, h := IsConjugate(G, gset, x, 1);
        Append(~sigma_ref, [ g^h : g in sigma ]);
    end for;

    // Basepoint switch if necessary; we want the "good" cycle to be above 0
    if bp eq 2 then
        sigma_ref := [ S3Action(Sym(3)!(1,2,3), sigma) : sigma in sigma_ref ];
    end if;
    if bp eq 3 then
        sigma_ref := [ S3Action(Sym(3)!(1,3,2), sigma) : sigma in sigma_ref ];
    end if;
    return sigma_ref;
end intrinsic;

intrinsic PointedRefinementSet(sigma::SeqEnum, bp::RngIntElt, ln::RngIntElt, aut::RngIntElt) -> SeqEnum
    {Given a permutation triple sigma computes the cycles of length ln in
    sigma[bp] up to simultaneous conjugation in Sym(d).  Here bp specifies in
    which permutation we mark a cycle, i.e., bp := 1,2,3 corresponds to sigma0,
    sigma1, sigmaoo (default is sigma0). After this, the special point is moved
    to 1 in the first permutation, that is, it is above 0.}
    cycles := CyclesOverBasePoint(sigma, bp, ln, aut);
    return PointedRefinementSetFromCycles(sigma, bp, cycles);
end intrinsic;

intrinsic SomeMinimalPointedRefinementSet(sigma::SeqEnum[GrpPermElt]) -> SeqEnum[GrpPermElt]
    {Given a triple sigma, find a small set of pointed representatives with
    respect to some branch order. The special point is always 1 in the first
    permutation, that is, it is above 0.}

    /* In the generic case that there is a point with unique ramification
     * index, we return that */
    for bp in [1..#sigma] do
        for tup in CycleStructure(sigma[bp]) do
            if tup[2] eq 1 then
                ln := tup[1];
                return PointedRefinementSet(sigma, bp, ln, 1), bp, ln, 1;
            end if;
        end for;
    end for;

    /* In other cases we are inefficient and just try everything */
    N := Infinity();
    for bp in [1..#sigma] do
        done := [ ];
        for cycle in CycleDecomposition(sigma[bp]) do
            ln := #cycle;
            aut := #PointedAutomorphismGroup(sigma : bp := bp, sh := cycle[1]);
            /* Stop if we hit the minimum */
            if not [ ln, aut ] in done then
                cycles := CyclesOverBasePoint(sigma, bp, ln, aut);
                if #cycles eq 1 then
                    return PointedRefinementSetFromCycles(sigma, bp, cycles), bp, ln, aut;
                end if;
                Append(~done, [ ln, aut ]);
            end if;

            /* Otherwise we update the smallest set so far if needed */
            if #cycles lt N then
                N := #cycles;
                refs0 := PointedRefinementSetFromCycles(sigma, bp, cycles);
                bp0 := bp; ln0 := ln; aut0 := aut;
            end if;
        end for;
    end for;
    return refs0, bp0, ln0, aut0;
end intrinsic;

intrinsic AllMinimalPointedRefinementSets(sigma::SeqEnum[GrpPermElt]) -> SeqEnum[GrpPermElt]
    {Given a triple sigma, find all small sets of pointed representatives with
    respect to some branch order. The special point is always 1 in the first
    permutation, that is, it is above 0.}

    N := Infinity();
    refss := [ ];
    for bp in [1..#sigma] do
        done := [ ];
        for cycle in CycleDecomposition(sigma[bp]) do
            ln := #cycle;
            aut := #PointedAutomorphismGroup(sigma : bp := bp, sh := cycle[1]);
            if not [ ln, aut ] in done then
                cycles := CyclesOverBasePoint(sigma, bp, ln, aut);
                if #cycles lt N then
                    N := #cycles;
                    refss := [ PointedRefinementSetFromCycles(sigma, bp, cycles) ];
                elif #cycles eq N then
                    Append(~refss, PointedRefinementSetFromCycles(sigma, bp, cycles));
                end if;
                Append(~done, [ ln, aut ]);
            end if;
        end for;
    end for;
    return refss;
end intrinsic;


intrinsic MinimalPointedRefinementSets(sigmas::SeqEnum[SeqEnum[GrpPermElt]]) -> SeqEnum[SeqEnum[GrpPermElt]]
    {Given a sequence of triples sigmas, find a small set of pointed
    representatives with respect to some branch order. The special point is
    always 1 in the first permutation, that is, it is above 0.}
    if #sigmas eq 0 then
        return [ ];
    end if;

    /* We first consider the first element of sigmas and point the rest
     * analogously. Note that there are likely better approaches if the passport
     * consists of multiple orbits with respect to the Galois action. Such
     * approaches have not been implemented yet. */
    sigma_ref, bp, ln, aut := SomeMinimalPointedRefinementSet(sigmas[1]);
    sigmas_ref := sigma_ref;
    for k in [2..#sigmas] do
        sigmas_ref cat:= PointedRefinementSet(sigmas[k], bp, ln, aut);
    end for;
    return sigmas_ref;
end intrinsic;

/* Representatives for a single triple of ambient conjugacy classes: */

function CompareClassesForPassportRepresentatives(tup1, tup2);
    return tup2[1][1] - tup1[1][1];
end function;

intrinsic SortForPassportRepresentatives(tups::SeqEnum[SeqEnum[Tup]]) -> SeqEnum[SeqEnum[Tup]]
    {Sorts a list of cycle structures in such a way that those with large
    cycles go first.}
    return Sort(tups, CompareClassesForPassportRepresentatives);
end intrinsic;

intrinsic PassportRepresentatives(G::GrpPerm, reps::SeqEnum[GrpPermElt] : Pointed := false, Weak := false, Optimize := true) -> SeqEnum
    {Given a transitive permutation group G of degree d and representatives
    reps of conjugacy classes of the normalizer N of G in Sym(d), return
    representatives in the corresponding coarse passport with conjugacy classes
    in N.
    Setting Pointed to true will give a small set of pointings that is stable
    under Galois.
    Setting Weak to true will eliminate the action of Sym(3).
    Setting Optimize to true will reorder the conjugacy classes first for a
    potential gain in speed.}
    assert #reps eq 3;
    assert IsTransitive(G);
    N := NormalizerInAmbient(G);

    // Optimize applies the action of S3 in such a way that large elements come
    // first; this is better for PassportLemma.
    if Optimize then
        cycstrs_sorted, perm := SortForPassportRepresentatives([ CycleStructure(rep) : rep in reps ]);
        reps_new := S3Action(perm, reps);
    else
        reps_new := reps;
    end if;

    // We now apply PassportLemma, take the solutions that we want, and
    // transform back if necessary.
    pairs := PassportLemma(G, [ reps_new[1], reps_new[2] ]);
    triples := [ [ pair[1], pair[2], (pair[2]*pair[1])^(-1) ] : pair in pairs ];
    sigmas := [ triple : triple in triples | IsConjugate(N, triple[3], reps_new[3]) ];
    if Optimize then
        sigmas := [ S3Action(perm^(-1), sigma) : sigma in sigmas ];
    end if;

    if Weak then
        sigmas := [ sigmas[i] : i in [1..#sigmas] | &and([ not IsWeaklyIsomorphic(N, sigmas[i], sigmas[j]) : j in [1..i-1] ]) ];
    end if;
    if Pointed then
        sigmas := MinimalPointedRefinementSets(sigmas);
    end if;
    return sigmas;
end intrinsic;

intrinsic PassportRepresentatives(G::GrpPerm, CCs::SeqEnum[Tup] : Pointed := false, Weak := false, Optimize := true) -> SeqEnum
    {Given a transitive permutation group G of degree d and conjugacy classes
    CCs of the normalizer N of G in Sym(d), return representatives in the
    corresponding coarse passport with conjugacy classes in N.
    Setting Pointed to true will give a small set of pointings that is stable
    under Galois.
    Setting Weak to true will eliminate the action of Sym(3).
    Setting Optimize to true will reorder the conjugacy classes first for a
    potential gain in speed.}
    return PassportRepresentatives(G, [ CC[3] : CC in CCs ] : Pointed := Pointed, Weak := Weak, Optimize := Optimize);
end intrinsic;

/* Representatives given either cycle types or a single dessin: */

// TODO: Right now this function is not as clever as it could be. A
// desymmetrization, as in the case of the main function, should be done. This
// is not hard (symmetrize initial data, then desymmetrize again by the action
// of S3) but for later work. It does main that calling the main function with
// specifies partitions is better than invoking this one... except if
// calculating the character table takes a lot of time.
intrinsic PassportRepresentatives(G::GrpPerm, cycstrs::SeqEnum[SeqEnum] : Pointed := false, Weak := false, Optimize := true) -> SeqEnum
    {Given a transitive permutation group G of degree d and a sequence
    (cycstrs) containing 3 partitions of d, return all permutation triples in
    the corresponding passport up to simultaneous conjugacy in Sym(d).
    Setting Pointed to true will give a small set of pointings that is stable
    under Galois.
    Setting Weak to true will eliminate the action of Sym(3).
    Setting Optimize to true will reorder the conjugacy classes first for a
    potential gain in speed.}
    assert #cycstrs eq 3;
    // Format conversion:
    if Type(cycstrs[1][1]) eq RngIntElt then
        cycstr_tups := [ Reverse([ < n, #[ x : x in cycstr | x eq n ] > : n in Set(cycstr) ]) : cycstr in cycstrs ];
    else
        cycstr_tups := cycstrs;
    end if;
    N := NormalizerInAmbient(G);
    if Optimize then
        cycstr_tups, perm := SortForPassportRepresentatives(cycstr_tups);
    end if;

    // Main algorithm
    // TODO: Please check that this line is correct and that no bigger set is
    // needed.
    CCs := [ CC[3] : CC in ConjugacyClassesModAmbient(G, N) ];
    splittings := [ [ CC : CC in CCs | CycleStructure(CC) eq cycstr_tup ] : cycstr_tup in cycstr_tups[1..2] ];
    CP := CartesianProduct(splittings);
    sigmas := [];
    for tup in CP do
        pairs := PassportLemma(G, [ rep : rep in tup ]);
        sigmas_new := [ [ pair[1], pair[2], (pair[2]*pair[1])^(-1) ] : pair in pairs ];
        sigmas_new := [ s : s in sigmas_new | CycleStructure(s[3]) eq cycstr_tups[3] ];
        sigmas cat:= sigmas_new;
    end for;
    if Optimize then
        sigmas := [ S3Action(perm^(-1), sigma) : sigma in sigmas ];
    end if;

    if Weak then
        sigmas := [ sigmas[i] : i in [1..#sigmas] | &and([ not IsWeaklyIsomorphic(N, sigmas[i], sigmas[j]) : j in [1..i-1] ]) ];
    end if;
    if Pointed then
        sigmas := MinimalPointedRefinementSets(sigmas);
    end if;
    return sigmas;
end intrinsic;

intrinsic PassportRepresentatives(sigma::SeqEnum[GrpPermElt] : Pointed := false, Weak := false, Optimize := true) -> SeqEnum
    {Given a dessin sigma in degree d, return representatives in the
    corresponding coarse passport.
    Setting Pointed to true will give a small set of pointings that is stable
    under Galois.
    Setting Weak to true will eliminate the action of Sym(3).
    Setting Optimize to true will reorder the conjugacy classes first for a
    potential gain in speed.}
    assert #sigma eq 3;
    S := Sym(Degree(Parent(sigma[1])));
    G := sub<S | [ S ! s : s in sigma]>;
    return PassportRepresentatives(G, [ CycleStructure(s) : s in sigma ] : Pointed := Pointed, Weak := Weak, Optimize := Optimize);
end intrinsic;

/* Representatives for all triples of ambient conjugacy classes: */

function CheckCycleStructures(cycstrs : genus := -1, only_hyperbolic := false, abc := [], partition_tups := [])
    // Symmetrized version
    checks := [];

    if genus ge 0 then
        d := &+[ &*cyc : cyc in cycstrs[1] ];
        Append(~checks, 2*genus - 2 eq -2*d + &+[ &+[(cyc[1] - 1)*cyc[2] : cyc in cycstr ] : cycstr in cycstrs ]);
    end if;
    if only_hyperbolic then
        orders := [ LCM([ cyc[1] : cyc in cycstr ]) : cycstr in cycstrs ];
        Append(~checks, &+[ 1/order : order in orders] lt 1);
    end if;

    if #abc ne 0 then
        orders := [ LCM([ cyc[1] : cyc in cycstr ]) : cycstr in cycstrs ];
        check := true;
        for n1 in Set(abc) diff {0} do
            if #[ order : order in orders | order eq n1 ] lt #[ n2 : n2 in abc | n2 eq n1 ] then
                check := false;
            end if;
        end for;
        Append(~checks, check);
    end if;

    if #partition_tups ne 0 then
        check := &and[ part in cycstrs : part in partition_tups ];
        Append(~checks, check);
    end if;
    if #checks eq 0 then
        return true;
    end if;
    return &and(checks);
end function;

function IsInLexicographicalOrderSubroutine(L, M)

return L le M;

end function;

function IsInLexicographicalOrder(L)

return &and([ IsInLexicographicalOrderSubroutine(L[i], L[i + 1]) : i in [1..(#L - 1)] ]);

end function;

// TODO: This function also admits loads of speedups. Skipped.
intrinsic PassportRepresentatives(G::GrpPerm : Pointed := false, Weak := false, genus := -1, only_hyperbolic := false, abc := [], partitions := []) -> SeqEnum
    {Given a transitive subgroup G of Sym(d), this function returns a complete
    list of coarse passports for G, ordered by cycle type.
    If genus ge 0, return only passports of specified genus.
    If only_hyperbolic, return only hyperbolic triples.
    If abc is specified, returns only triples with orders a,b,c (zero entries
    ignored; may supply less than three entries).
    If partitions is specified, return only triples whose cycle structures are
    one of the cycle structures that is described (empty entries ignored).
    Setting Pointed to true will give a small set of pointings that is stable
    under Galois; this will enlarge the number of resulting triples in general.
    Setting Weak to true will only give representatives up to the action of
    Sym(3).}

    // Conversion:
    if partitions ne [] then
        if Type(partitions[1][1]) eq RngIntElt then
            partition_tups := [ Reverse([ < n, #[ x : x in partition | x eq n ] > : n in Set(partition) ]) : partition in partitions ];
        else
            partition_tups := partitions;
        end if;
    else
        partition_tups := partitions;
    end if;

    // Setting the (desymmetrized) stage:
    S := SymmetricGroup(Degree(G));
    N := NormalizerInAmbient(G);
    CCsModN := ClassRepresentativesModAmbient(G, N);
    vprintf Passport : "CCsModN = \n%o\n", CCsModN;
    vprintf Passport : "#CCsModN = %o\n", #CCsModN;
    indss := CartesianPower({1..#CCsModN}, 3);
    indss := [ [ elt : elt in tup ] : tup in indss ];
    indss := [ inds : inds in indss | CheckCycleStructures([ CycleStructure(CCsModN[ind]) : ind in inds ] : genus := genus, only_hyperbolic := only_hyperbolic, abc := abc, partition_tups := partition_tups) ];
    indss := S3Representatives(indss, G, N);
    indss12 := [ [ inds[1], inds[2] ] : inds in indss ];
    indss12 := [ elt : elt in Set(indss12) ];
    passports_by_ccs := [];
    vprint Passport : "Sorted conjugacy class indices modulo ambient:";
    vprint Passport : indss;
    vprintf Passport : "#indss = %o\n", #indss;

    // Run over the first two entries and sort into conjugacy triples above:
    for inds12 in indss12 do
        pairs := PassportLemma(G, [ CCsModN[ind] : ind in inds12 ]);
        if #pairs ne 0 then
            vprint Passport : "Pair found for", inds12;
            vprintf Passport : "Pairs = \n%o\n", pairs;
        end if;
        sigmas_new := [ [ pair[1], pair[2], (pair[2]*pair[1])^(-1) ] : pair in pairs ];
        // Store by third entry:
        for sigma in sigmas_new do
            CCinds := Append(inds12, ConjugacyClassModAmbientNumber(G, N, sigma[3]));
            if CCinds in indss then
                create_new := true;
                for i:=1 to #passports_by_ccs do
                    if passports_by_ccs[i][1] eq CCinds then
                        Append(~passports_by_ccs[i][2], sigma);
                        create_new := false;
                    end if;
                end for;
                if create_new then
                    Append(~passports_by_ccs, [* CCinds, [ sigma ] *]);
                end if;
            end if;
        end for;
    end for;
    vprint Passport : "After passport lemma and first sorting:";
    vprint Passport : passports_by_ccs;
    vprintf Passport : "#passports = %o\n", #passports_by_ccs;
    vprintf Passport : "sizes = %o\n", [#pass[2] : pass in passports_by_ccs];

    // Testing the entries for compatibility demands and discarding failures:
    passports_by_ccs := [ [* passport[1], [ sigma : sigma in passport[2] | CheckCycleStructures([ CycleStructure(s) : s in sigma ] : genus := genus, only_hyperbolic := only_hyperbolic, abc := abc, partition_tups := partition_tups) ] *] : passport in passports_by_ccs ];
    passports_by_ccs := [ passport : passport in passports_by_ccs | passport[2] ne [] ];
    vprint Passport : "After throwing away entries that do not stand the test:";
    vprintf Passport : "#passports = %o\n", #passports_by_ccs;
    vprintf Passport : "sizes = %o\n", [#pass[2] : pass in passports_by_ccs];

    if Weak then
        passports_by_ccs_new := [ ];
        for passport in passports_by_ccs do
            ccs, sigmas := Explode(passport);
            if ccs[1] eq ccs[2] or ccs[2] eq ccs[3] then
                sigmas := [ sigmas[i] : i in [1..#sigmas] | &and([ not IsWeaklyIsomorphic(N, sigmas[i], sigmas[j]) : j in [1..i-1] ]) ];
            end if;
            Append(~passports_by_ccs_new, [* ccs, sigmas *]);
        end for;
        passports_by_ccs := passports_by_ccs_new;
        vprint Passport : "After removing weak isomorphisms:";
        vprint Passport : passports_by_ccs;
        vprintf Passport : "#passports = %o\n", #passports_by_ccs;
        vprintf Passport : "sizes = %o\n", [#pass[2] : pass in passports_by_ccs];
    end if;

    // Symmetrizing to get all possible triples of conjugacy classes:
    if not Weak then
        for passport in passports_by_ccs do
            for g in Sym(3) do
                new_entry := S3Action(g, passport[1], G, N);
                if not new_entry in [ passport[1] : passport in passports_by_ccs ] then
                    Append(~passports_by_ccs, [* new_entry, [ S3Action(g, sigma) : sigma in passport[2] ] *]);
                end if;
            end for;
        end for;
        vprint Passport : "After symmetrization:";
        vprint Passport : passports_by_ccs;
        vprintf Passport : "#passports = %o\n", #passports_by_ccs;
        vprintf Passport : "sizes = %o\n", [#pass[2] : pass in passports_by_ccs];
    end if;

    // Throwing together all passports with equal cycle structures:
    passports_by_cycstrs := [];
    for passport_by_ccs in passports_by_ccs do
        cycstrs := [ CycleStructure(CCsModN[ind]) : ind in passport_by_ccs[1] ];
        create_new := true;
        for i:=1 to #passports_by_cycstrs do
            if passports_by_cycstrs[i][1] eq cycstrs then
                create_new := false;
                passports_by_cycstrs[i][2] cat:= passport_by_ccs[2];
            end if;
        end for;
        if create_new then
            Append(~passports_by_cycstrs, [* cycstrs, passport_by_ccs[2] *]);
        end if;
    end for;

    if not Weak then
        passports_by_cycstrs := [ pair : pair in passports_by_cycstrs | IsInLexicographicalOrder(pair[1]) ];
    end if;

    vprint Passport : "After throwing cycle structures together:";
    vprint Passport : passports_by_cycstrs;
    vprintf Passport : "#passports = %o\n", #passports_by_cycstrs;
    vprintf Passport : "sizes = %o\n", [#pass[2] : pass in passports_by_cycstrs];

    // Return pointings if so indicated
    if Pointed eq true then
        passports_by_cycstrs := [ [* passport[1], MinimalPointedRefinementSets(passport[2]) *] : passport in passports_by_cycstrs ];
    end if;

    return passports_by_cycstrs;
end intrinsic;

/* Representatives for all triples of ambient conjugacy classes of all groups of a given degree: */

intrinsic PassportRepresentatives(d::RngIntElt : Pointed := false, Weak := false, Primitive := false, genus := -1, only_hyperbolic := false, abc := [], partitions := []) -> SeqEnum
    {Given a degree d, this function determines a list of coarse passports for
    all transitive groups of degree d.
    If genus ge 0, return only passports of specified genus.
    If only_hyperbolic, return only hyperbolic triples.
    If abc is specified, returns only triples with orders a,b,c.
    If partitions is specified, return only triples whose cycle structures are
    of one of the cycle structures that is described (empty entries ignored).
    Setting Pointed to true will give a small set of pointings that is stable
    under Galois; this will enlarge the number of resulting triples in general.
    Setting Weak to true will eliminate the action of Sym(3).}
    if Primitive then
        db := PrimitiveGroups(d);
    else
        db := TransitiveGroupDatabase(d);
    end if;
    return [ [* G, PassportRepresentatives(G : Pointed := Pointed, Weak := Weak, genus := genus, only_hyperbolic := only_hyperbolic, abc := abc, partitions := partitions) *] : G in db ];
end intrinsic;
