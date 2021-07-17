/*
----------------------------------------------------------------------------
----------------------------------------------------------------------------
Coset Reps
Input:
	Delta: Containing triangle group
	Gamma: Triangle subgroup
Output:
	return: A sequence of coset representatives for Gamma in Delta and
	  the coset graph.
----------------------------------------------------------------------------
*/

import "../../../../magma/package/Geometry/GrpPSL2/GrpPSL2Shim/domain.m" :
  InternalShimuraInterreduce;

intrinsic CosetRepresentatives(Gamma::GrpPSL2Tri : Al := "Petal", FindSmallestCosets := false) -> SeqEnum
  {Returns a sequence of coset representatives for Gamma in its
   containing triangle group Delta.
   If Al eq "Petal", then prefer 'a' moves; otherwise,
   "Full" gives 'a' and 'b' moves.}

  Delta := ContainingTriangleGroup(Gamma);

  if assigned Gamma`TriangleCosets then
    return Gamma`TriangleCosets, Gamma`TriangleCosetGraph, Gamma`TriangleSidePairing;
  end if;

  sigma := DefiningPermutation(Gamma);
  sigma0, sigma1, sigmaoo := Explode(sigma);
  pi := DefiningPermutationRepresentation(Gamma);

  d := IndexDegree(Gamma);
  G := MultiDigraph<d | >;
  AssignLabel(~G, Vertices(G)[1], Delta!1);

  sidepairing := [];
  DD := UnitDisc(Delta);
  D0 := DD!0;
  FDDelta := FundamentalDomain(Delta, DD);

  if Al eq "Full" then
    frontier := [1];

    // Build basic graph
    epses := [Delta.1, Delta.1^-1, Delta.2, Delta.2^-1];
    while not IsEmpty(frontier) do
      dists := [Distance(D0, Label(Vertices(G)[i])*D0) : i in frontier];
      _, jind := Min(dists);
      j := frontier[jind];
      vprint Shimura : [Label(Vertices(G)[i]) : i in frontier];
      vprint Shimura : dists;
      vprintf Shimura : "Taking jind = %o, with distance %o and label %o\n", jind, dists[jind], Label(Vertices(G)[j]);
      Remove(~frontier, jind);

      alphaj := Label(Vertices(G)[j]);
      for eps in epses do
        i := 1^(pi(alphaj*eps));
        AddEdge(~G, Vertices(G)[j], Vertices(G)[i], eps);
        if IsLabelled(Vertices(G)[i]) then
          alphai := Label(Vertices(G)[i]);
          gamma := alphaj*eps*alphai^-1;
          if not IsScalar(Quaternion(gamma)) then
            Append(~sidepairing, [* gamma, <j, eps>, <i, eps^-1> *]);
          end if;
        else
          AssignLabel(~G, Vertices(G)[i], alphaj*eps);
          Append(~frontier, i);
        end if;
      end for;
    end while;

  else // Al eq "Petal"
    frontierA := [1];
    frontierB := [1];

    finishAllAs := function(G, frontierA, frontierB, sidepairing);
      while not IsEmpty(frontierA) do
        dists := [Distance(D0, Label(Vertices(G)[i])*D0) : i in frontierA];
        _, jind := Min(dists);
        j := frontierA[jind];
        vprintf Shimura : "A: Taking j = %o, with distance %o and label %o\n",
            j, RealField(6)!dists[jind], Label(Vertices(G)[j]);
        Remove(~frontierA, jind);

        alphaj := Label(Vertices(G)[j]);
        donepos := false;
        doneneg := false;
        ind := 0;
        // rotate around the chosen vertex
        while not (donepos and doneneg) do
          ind +:= 1;
          epspows := [];
          if not donepos then
            Append(~epspows, ind);
          end if;
          if not doneneg then
            Append(~epspows, -ind);
          end if;
          for epspow in epspows do
            eps := Delta.1^Sign(epspow);
            jp := j^pi(Delta.1^(epspow-Sign(epspow)));
            alphajp := Label(Vertices(G)[jp]);
            i := 1^(pi(alphajp*eps));
            AddEdge(~G, Vertices(G)[jp], Vertices(G)[i], eps);

            vprintf Shimura : "A: Rotating by delta_a^%o, ", epspow;

            if IsLabelled(Vertices(G)[i]) then
              alphai := Label(Vertices(G)[i]);

              gamma := alphajp*eps*alphai^-1;
              if not IsScalar(Quaternion(gamma)) then
                Append(~sidepairing, [* gamma, <jp, eps>, <i, eps^-1> *]);
              end if;
              if epspow gt 0 then
                donepos := true;
              end if;
              if epspow lt 0 then
                doneneg := true;
              end if;

              vprintf Shimura : "already identified %o (label %o)", i, Label(Vertices(G)[i]);

              if not IsScalar(Quaternion(gamma)) then
                vprintf Shimura : ", sidepairing %o\n", gamma;
              else
                vprintf Shimura : "\n";
              end if;
            else
              AssignLabel(~G, Vertices(G)[i], alphajp*eps);
              Append(~frontierB, i);

              vprintf Shimura : "new coset %o\n", i;
            end if;
          end for;
        end while;
      end while;
      return G, frontierA, frontierB, sidepairing;
    end function;

    // Build basic graph
    while not IsEmpty(frontierA cat frontierB) do
      G, frontierA, frontierB, sidepairing := finishAllAs(G, frontierA, frontierB, sidepairing);

      // Now try a "B"
      dists := [Distance(D0, Label(Vertices(G)[i])*D0) : i in frontierB];
      _, jind := Min(dists);
      j := frontierB[jind];
      vprintf Shimura : "B: Taking j = %o, with distance %o and label %o\n",
            j, RealField(6)!dists[jind], Label(Vertices(G)[j]);
      Remove(~frontierB, jind);

      alphaj := Label(Vertices(G)[j]);
      for epspow in [1,-1] do
        eps := Delta.2^epspow;
        vprintf Shimura : "B: Rotating by delta_b^%o, ", epspow;

        i := 1^(pi(alphaj*eps));
        AddEdge(~G, Vertices(G)[j], Vertices(G)[i], eps);
        if IsLabelled(Vertices(G)[i]) then
          alphai := Label(Vertices(G)[i]);
          gamma := alphaj*eps*alphai^-1;
          if not IsScalar(Quaternion(gamma)) then
            Append(~sidepairing, [* gamma, <j, eps>, <i, eps^-1> *]);
          end if;

          vprintf Shimura : "already identified %o (label %o)", i, Label(Vertices(G)[i]);
          if not IsScalar(Quaternion(gamma)) then
            vprintf Shimura : ", sidepairing %o\n", gamma;
          else
            vprintf Shimura : "\n";
          end if;
        else
          AssignLabel(~G, Vertices(G)[i], alphaj*eps);
          Append(~frontierA, i);
          Append(~frontierB, i);

          vprintf Shimura : "new coset %o\n", i;
        end if;

        G, frontierA, frontierB, sidepairing := finishAllAs(G, frontierA, frontierB, sidepairing);
      end for;
    end while;
  end if;

  if FindSmallestCosets then
    // Find smallest cosets
    gammas := [d[1] : d in sidepairing];
    DD := UnitDisc(Gamma);
    domain := ChangeUniverse(gammas, Gamma);
    domain := [gamma : gamma in domain | not IsScalar(Quaternion(gamma))];

    vprintf Shimura : "Interreducing...\n";
    bl, domainnew := InternalShimuraInterreduce(domain, DD : FindEnveloper := false);

    m := #domain;
    mseq := [1,1];
    while not bl do
      vprintf Shimura: "%o ", mseq;
      gamma := Gamma!Id(Gamma);
      for ms in mseq do
        gamma := gamma*domain[ms];
      end for;
      deltared := ShimuraReduceUnit(gamma, domainnew, DD);
      if not IsScalar(Quaternion(deltared[1])) then
        bl, domainnew := InternalShimuraInterreduce(domainnew cat [deltared[1],
                                 deltared[1]^-1], DD : FindEnveloper := false);
      end if;
      mseq[1] +:= 1;
      i := 1;
      while i le #mseq and mseq[i] gt m do
        mseq[i] := 1;
        i +:= 1;
        if i le #mseq then
          mseq[i] +:= 1;
        end if;
      end while;
      if i gt #mseq then
        mseq := mseq cat [1];
      end if;
    end while;
    domain := domainnew;

    for j := 1 to d do
      v := Vertices(G)[j];
      alpha := Label(v);

      repeat
        passed := true;

        alphadists := [Abs(ComplexValue(alpha*w)) : w in FDDelta];
        maxadist := Max(alphadists);
        for gamma in domain do
          gammaalphadists := [Abs(ComplexValue(gamma*alpha*w)) : w in FDDelta];
          maxgadist := Max(gammaalphadists);
          if maxgadist lt maxadist then
            alpha := gamma*alpha;
            vprintf Shimura : "alphadists = %o\n", alphadists;
            vprintf Shimura : "gammaalphdists = %o\n", gammaalphadists;
            vprintf Shimura : "Shrinking vertex %o by %o!\n", j, gamma;
            AssignLabel(~G, v, alpha);
            for k := 1 to #sidepairing do
              side := sidepairing[k];
              if side[2][1] eq j then
                sidepairing[k][1] := gamma*side[1];
              elif side[3][1] eq j then
                sidepairing[k][1] := side[1]*gamma^-1;
              end if;
            end for;
            passed := false;
            break;
          end if;
        end for;
      until passed;
    end for;
  end if;

  cosets := [Label(Vertices(G)[i]) : i in [1..d]];

  Gamma`TriangleCosets := cosets;
  Gamma`TriangleCosetGraph := G;
  Gamma`TriangleSidePairing := sidepairing;

  return cosets, G, sidepairing;
end intrinsic;

intrinsic IdentifyCoset(Gamma::GrpPSL2Tri, delta::GrpPSL2Elt) -> GrpPSL2Elt, RngIntElt
  {Returns the coset Gamma*alpha_i that delta belongs, together with its index i.}
  // or the other way around, or with inverses...

  require delta in ContainingTriangleGroup(Gamma) :
                   "delta must belong to containing triangle group";

  cosets := CosetRepresentatives(Gamma);
  pi := DefiningPermutationRepresentation(Gamma);

  i := 1^pi(delta);
  return cosets[i], i;
end intrinsic;
