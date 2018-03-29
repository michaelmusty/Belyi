FDReduce := function(wp, Gamma);
  // Setup
  HH := UpperHalfPlane();
  D := Parent(wp);
  zp := DiscToPlane(HH, wp);

  // Reduce to fundamental domain
  deltaH, w, jind := TriangleReduceToFundamentalDomain(Gamma, wp);

  deltaHmat := Matrix(deltaH);  // Default is matrix on upper half-plane
  jAut := deltaHmat[2,1]*ComplexValue(zp) + deltaHmat[2,2];  // automorphy factor

  return w, deltaH, jAut, jind;
end function;




intrinsic TrianglePowerSeriesBasis(Gamma::GrpPSL2, k::RngIntElt :
                                   prec := 0, N := 0, Q := 0, dim := 0,
                                   Federalize := true, Al := "Arnoldi", UseRamOffsets := true) -> Any
{prec is the precision to compute in (must be at least precision of the unit disc;
 N is the number of terms in the power series basis;
 dimension is of the subspace computed ("top terms");
 Federalize uses multiple centers;
 Al is either "Arnoldi" (uses Arnoldi iteration) or
 "Full" (computes the full matrix and the SVD).}

  require IsTriangleSubgroup(Gamma) : "Gamma must be a triangle subgroup";
  require k gt 0 and k mod 2 eq 0 : "k >= 2 must be even";

  DD := TriangleUnitDisc(Gamma);
  if prec ne 0 then
    if prec ne DD`prec then
      print "WARNING: precision input into TrianglePowerSeriesBasis is different than specified in Gamma";
      DD := TriangleUnitDisc(Gamma : Precision := prec);
    end if;
  else // prec eq 0 
    prec := DD`prec;
  end if;
  p := Center(DD);

  vprintf Shimura : "Using unit disc with precision %o and center %o\n", DD`prec, p;

  /*
  if prec lt DD`prec then
    prec := DD`prec;  // use precision of unit disc
  else
    assert DD`prec ge prec;  // must have enough digits
  end if;
  */
  CC<I> := ComplexField(prec);
  pi := Pi(CC);
  eps_thresh := RealField(CC)!10^(-prec+2*Floor(Log(prec)));  // threshold after which we accept the answer
  Gamma`TriangleNumericalPrecision := prec;
  Gamma`TriangleNumericalEpsilon := 10^(-prec/2); // or should we take eps_thresh defined above?

  indat := [* k, prec, N, Q, dim, Federalize, Al, UseRamOffsets *];

  vprintf Shimura : "Using working precision %o with eps_thresh = %o\n",
      prec, RealField(6)!eps_thresh;

  if assigned Gamma`TrianglePowserBases then
    // check if already computed
    for powserdat in Gamma`TrianglePowserBases do
      if powserdat[1] eq [* k, prec, N, Q, dim, Federalize, Al, UseRamOffsets *] then
        return Explode(powserdat[2]);
      end if;
    end for;
  end if;

  Delta := ContainingTriangleGroup(Gamma);

  if Federalize then
    rho := Max([Abs(z) : z in FundamentalDomain(Delta, DD)]);
  else
    rho := Max([Abs(z) : z in FundamentalDomain(Gamma, DD)]);
  end if;

  vprintf Shimura : "Radius of series to be used: %o\n", RealField(6)!rho;

  // We now set the number of interpolation points or leave it as the default
  N0 := Ceiling(Log(10^-prec)/Log(rho));
  if N eq 0 then
    N := N0;
  elif N lt N0 then
    vprintf Shimura : "WARNING: N = %o is smaller than needed %o\n", N, N0;
  end if;

  Q := Max(Q, N+2*Ceiling(Log(N))); //wild guess

  vprintf Shimura : "Taking N = %o and Q = %o\n", N, Q;

  sigma := DefiningPermutation(Gamma);
  if UseRamOffsets then
    a := DefiningABC(Gamma)[1];
    es := [a div #c : c in CycleDecomposition(sigma[1])];
    ss := [((k div 2)*(e-1)) mod e : e in es];
  else
    es := [1 : c in CycleDecomposition(sigma[1])];
    ss := [0 : e in es];
  end if;

  vprintf Shimura : "Ramification degrees e = %o and offsets s = %o\n", es, ss;

  if Federalize then
    deltas := TriangleCosetRepresentatives(Gamma);
    sigma := DefiningPermutation(Gamma);
    //the first entry in each cycle of sigma0
    //E.g., sigma0 = (13)(256)(4), then vinds = [1,2,4]
    vinds := [c[1] : c in CycleDecomposition(sigma[1])];
    nv := #vinds;

    //If i is in the kth cycle of sigma0, then the ith entry of whichcoset is k
    //E.g., if sigma0 = (13)(256)(4), then whichcoset = [1,2,1,3,2,2]
    whichcoset := [0 : i in [1..#deltas]];
    cyc := CycleDecomposition(sigma[1]);
    for i := 1 to #cyc do
      c := cyc[i];
      for cc in c do
        whichcoset[cc] := i;
      end for;
    end for;
    assert 0 notin whichcoset;

    //make unit discs centered at the white dots, which are translates of the origin determined by the entries of vinds
    DDs := [DD] cat [UnitDisc( : Center := deltas[v]*p, Precision := prec) : v in vinds[2..nv]];

    vprintf Shimura : "Indices of vertices to be used: %o\n", vinds;
    vprintf Shimura : "Coset identifiers: %o\n", whichcoset;
  else
    deltas := TriangleCosetRepresentatives(Gamma);
    whichcoset := [1 : i in [1..#deltas]];
    nv := 1;
    DDs := [DD];
  end if;

  Gamma`TriangleWhichCoset := whichcoset;
  Gamma`TriangleDDs := DDs;

  wp_ms := [];
  jAut_z_ms := [];
  jinds := [];
  w_ms0 := [rho*Exp(2*pi*I*m/Q) : m in [1..Q]];

  maxwp := 0;
  vprintf Shimura : "Reducing to fundamental domain... ";
  vtime Shimura:
  if true then // so Magma will time as one chunk
    for i := 1 to nv do
      for m in [1..Q] do
        w_m := PlaneToDisc(DD, DiscToPlane(UpperHalfPlane(), DDs[i]!(w_ms0[m])));
        wp_m, gamma_m, jAut_z_m, jind := FDReduce(w_m, Gamma);
        wjind := whichcoset[jind];
        wp_mj := PlaneToDisc(DDs[wjind], DiscToPlane(UpperHalfPlane(), wp_m));
        assert Abs(wp_mj) le rho + eps_thresh;
        // assert Abs(wp_mj) le rho + Gamma`TriangleNumericalEpsilon; // wild guess
        maxwp := Max(Abs(wp_mj),maxwp);
        Append(~wp_ms, ComplexValue(wp_mj));
        Append(~jAut_z_ms, jAut_z_m^(-k));
        Append(~jinds, whichcoset[jind]);
      end for;
    end for;
  end if;

  vprintf Shimura : "Largest point had radius %o!\n", RealField(6)!maxwp;

  // adjust with factor rho
  w_ms0 := [w_m/rho : w_m in w_ms0];
  wp_ms := [wp_m/rho : wp_m in wp_ms];

  g := Genus(Gamma);
  if k eq 2 then
    fulldim := g;
  else
    fulldim := (k-1)*(g-1) + &+[ Floor(k/2*(1-1/e)) : e in Signature(Gamma)[2]];
  end if;
  require dim le fulldim : "dim must be less than fulldim =", fulldim;
  if dim eq 0 then
    dim := fulldim;
  end if;

  skipcoeffs := [0..fulldim-dim-1];
  NNs := [(N+1) div es[i] : i in [1..#es]];
  NNs[1] -:= #skipcoeffs;
  vprintf Shimura : "dim = %o, fulldim = %o, so skipping coeffs %o\n", dim, fulldim, skipcoeffs;

  Js := [* *];
  vprintf Shimura : "Computing Js... ";
  vtime Shimura:
  for i := 1 to nv do
    J := [];
    jaut := ChangeUniverse(jAut_z_ms[(i-1)*Q+1..i*Q], CC);
    for m in [1..Q] do
      jaut[m] /:= (1-w_ms0[m]*rho)^k*w_ms0[m]^ss[i];
    end for;

    w_ms0i := [w_m^es[i] : w_m in w_ms0];

    for n := 0 to ((N+1) div es[i])-1 do
      if i ne 1 or n notin skipcoeffs then // if i ne 1 then no conditions
        Append(~J, jaut);
      end if;
      for m in [1..Q] do
        jaut[m] /:= w_ms0i[m];
      end for;
    end for;
    J := Matrix(J);
    J := Transpose(J);
    Append(~Js, J);
  end for;

  if Federalize then
    // sort
    permut := [];
    Sort(~jinds, ~permut);
    permutseq := Eltseq(permut^-1);
    permutinvseq := Eltseq(permut);
    wp_ms_sorted := [wp_ms[permutinvseq[i]] : i in [1..nv*Q]];
  else
    permutseq := [1..NNs[1]];
    wp_ms_sorted := wp_ms;
  end if;

  wpinds := [1];
  for i := 2 to nv do
    Append(~wpinds, Index(jinds, i));
  end for;
  Append(~wpinds,#jinds+1);

  Wps := [* *];
  vprintf Shimura : "Computing Wps... ";
  vtime Shimura:
  for i := 1 to nv do
    Wp := [];
    wp_msi := wp_ms_sorted[wpinds[i]..wpinds[i+1]-1];
    Qi := #wp_msi;
    vandermonde := [CC | wp_msi[m]^ss[i]*(1-wp_msi[m]*rho)^k : m in [1..Qi]];

    wp_msi := [wp_m^es[i] : wp_m in wp_msi];
    for r := 0 to ((N+1) div es[i])-1 do
      if i ne 1 or r notin skipcoeffs then
        Append(~Wp, vandermonde);
      end if;
      for m := 1 to Qi do
        vandermonde[m] *:= wp_msi[m];
      end for;
    end for;
    Wp := Matrix(Wp);
    Append(~Wps, Wp);
  end for;

  //
  // Now solve
  //

  // ===========================================
  // Numerical eigenvalue might be better?  Should work on optimizing this.
  if Al eq "Arnoldi" then // use SVD on the Arnoldi subspace

    xout := [];
    for dim_cnt := 1 to dim do

      // Initialize
      q1 := [CC | rho^(ss[1]+n*es[1]) : n in [0..((N+1) div es[1])-1] | n notin skipcoeffs];
      for jdim := 1 to dim do
        if jdim ne dim_cnt then
          q1[jdim] := 0;
        end if;
      end for;
      q := [ Vector(q1 cat &cat[[CC | rho^(ss[i]+n*es[i]) : n in [0..NNs[i]-1]] : i in [2..nv]]) ];  // start

      x := [q[1]];
      q[1] /:= Sqrt(Norm(q[1]));

      h := [];

      i := 1;
      minsing := 0;
      err_arn := 0;
      yFound := false;
      ysol := [];
      repeat
        if yFound and minsing lt eps_thresh and i gt 1 then
          err_arn := Abs(Eltseq(ysol[1])[Degree(ysol[1])]);
        end if;
        i +:= 1;

        vprintf Shimura : "Arnoldi iteration %o... ", i;
        vtime Shimura:
        if true then // to get Magma timing

        // multiply by the matrix A
          qi := Eltseq(q[i-1]);
          qiind := 0;
          qis := [* *];
          for j := 1 to nv do
            Append(~qis, Vector(qi[qiind+1..qiind+NNs[j]])*Wps[j]);
            qiind +:= NNs[j];
          end for;
          qi := &cat[Eltseq(v) : v in qis];
          if Federalize then
            qi := [qi[permutseq[i]] : i in [1..nv*Q]];
          end if;
          qis := [* Vector(qi[(i-1)*Q+1..i*Q])*Js[i] : i in [1..nv] *];
          qi := Vector(&cat[Eltseq(v) : v in qis]);
          qi /:= Q;

          /* Test matrices
          Jx := ZeroMatrix(CC, (N+1)*nv, Q*nv);
          for i := 1 to nv do
            for r := 0 to N do
              for j := 1 to Q do
                Jx[(i-1)*Q+1+r,(i-1)*Q+j] := jAut_z_ms[(i-1)*Q+j]/w_ms0[j]^r;
              end for;
            end for;
          end for;
          Jx := Transpose(Matrix(Jx));

          Wpx := ZeroMatrix(CC, Q*nv, (N+1)*nv);
          for i := 1 to #jinds do
            for r := 0 to N do
              Wpx[i, (jinds[permutseq[i]]-1)*(N+1)+1+r] := wp_ms[i]^r;
            end for;
          end for;
          Wpx := Transpose(Matrix(Wpx));
          */

          q[i] := qi;

          Append(~h, []);
          for j := 1 to i-1 do
            h[i-1,j] := InnerProduct(q[i],q[j]);
            q[i] -:= h[i-1,j]*q[j];
          end for;
          h[i-1,i] := Sqrt(Norm(q[i]));
          q[i] /:= h[i-1,i];
          // zero fill
          for k := 1 to i-2 do
            h[k,i] := 0;
          end for;
        end if;

        if i lt 10 then
          yFound := false;
          continue;
        end if;

        // TO DO: This is wasteful!  Should reuse information from
        // previous iterations.  But in large examples, all of the time
        // will be spent above, so this should be not too bad.

        // TO DO: Estimate convergence of Arnoldi
        // restart or at least don't compute numerical kernel
        vprintf Shimura : "Numerical kernel %o... ", i;
        vtime Shimura:
        if true then
          H0 := ColumnSubmatrix(Matrix(h),i-1);
          ysol, sings := NumericalKernel_old(H0-1 : Epsilon := eps_thresh);
          minsingprev := minsing;
          minsing := Min([Abs(s) : s in sings]);
          vprintf Shimura : "min %o (of %o)... ", RealField(6)!minsing, #ysol;
          if #ysol ge 1 then
            yFound := true;
            vprintf Shimura: "\n%o\n", ChangeRing(ysol[1],ComplexField(6));
            Q0 := RowSubmatrix(Matrix(q),i-1);
            Append(~x, Matrix(ysol)*Q0);
          else
            yFound := false;
          end if;
        end if;

/*
        // restart?
        if i gt 20 then
          h := [];
          q := [q[#q]];
          i := 1;
        end if;
*/
      until yFound and (minsing lt eps_thresh and Abs(Eltseq(ysol[1])[Degree(ysol[1])]) gt err_arn);
      vprintf Shimura : "escaped with cutoff %o...\n", RealField(6)!Abs(Eltseq(ysol[1])[Degree(ysol[1])]);

      assert #ysol eq 1;  // Only one-dimensional kernel each time!?

      Append(~xout, x[#x]);
    end for;

  // ===========================================

  else // if Al eq "Full"
    // multiply out the matrix A
    Wp_full := Matrix(BlockDiagMat(<Wp : Wp in Wps>));
    J_full := Matrix(BlockDiagMat(<J : J in Js>));
    if Federalize then
      Pi := PermutationMatrix(CC, permutinvseq);
      vprintf Shimura : "Multiplying matrix... ";
      vtime Shimura:
      A := Wp_full*Pi*J_full/Q;
    else
      vprintf Shimura : "Multiplying matrix... ";
      vtime Shimura:
      A := Wp_full*J_full/Q;
    end if;

    vprintf Shimura : "Computing numerical kernel... ";
    vtime Shimura:
    x, sings := NumericalKernel_old(Matrix(A)-1 : Epsilon := eps_thresh);

    vprintf Shimura : "Singular values: %o\n",
        [RealField(6) | sing : sing in sings | Abs(sing) lt eps_thresh];

    assert #x eq dim; // Something is wrong: dimension of eigenspace not equal to dim?

    xout := x;

    minsing := Max([sing : sing in sings | Abs(sing) lt eps_thresh]);
  end if;

  // Fill and split
  xout_split := [];
  for i := 1 to #xout do
    xout_vecs := [];
    xoutseq := Eltseq(xout[i]);

    xouti := Eltseq(xoutseq[1..NNs[1]]);
    xoutii := [CC | ];
    nn := 1;
    for n := 0 to ((N+1) div es[1])-1 do
      if n in skipcoeffs then
        Append(~xoutii, 0);
      else
        Append(~xoutii, xouti[nn]*rho^-(ss[1]+n*es[1]));
        nn +:= 1;
      end if;
    end for;
    xout_vecs := [xoutii];
    xcnt := NNs[1];

    for j := 2 to nv do
      xouti := xoutseq[xcnt+1..xcnt+NNs[j]];
      xoutii := [xouti[n+1]*rho^-(ss[j]+n*es[j]) : n in [0..((N+1) div es[j])-1]];
      Append(~xout_vecs, xoutii);
      xcnt +:= NNs[j];
    end for;

    Append(~xout_split, xout_vecs);
  end for;

  // Normalize
  CCw<w> := PowerSeriesRing(CC, N+1);
  fout := [];
  for x in xout_split do
    f := [];
    for i := 1 to #x do
      xi := Eltseq(x[i]);
      fi := &+[xi[n+1]*w^(ss[i]+es[i]*n) : n in [0..#xi-1]];
      Append(~f, fi);
    end for;
    Append(~fout, f);
  end for;

  // Echelonize
  norm0fout := fout;
  for i := 1 to #norm0fout do
    f := norm0fout[i];
    for j := 1 to #f do
      fjes := AbsEltseq(f[j]);
      for n := 1 to #fjes do
        if Abs(fjes[n]) lt 10^(-4/5*prec) then
          fjes[n] := 0;
        end if;
      end for;
      norm0fout[i][j] := CCw!fjes;
    end for;
  end for;
  s := #skipcoeffs;
  E, T := EchelonForm(Matrix([[Coefficient(f[1],n) : n in [0..NNs[1]-1]] : f in norm0fout]));
  vprint Shimura : "Echelonize:", T;
  fout_ech := [ [] : i in [1..#fout]];

  for i := 1 to #fout[1] do
    M := Matrix([[Coefficient(f[i],n) : n in [0..N]] : f in fout]);
    Mout := T*M;
    for j := 1 to #fout do
      fout_ech[j] := fout_ech[j] cat [CCw!Eltseq(Mout[j])];
    end for;
  end for;

  dat := [* indat, [* fout_ech, minsing, fout *] *];
  if assigned Gamma`TrianglePowserBases then
    Append(~Gamma`TrianglePowserBases, dat);
  else
    Gamma`TrianglePowserBases := [dat];
  end if;

  return fout_ech, minsing, fout;
end intrinsic;
