//For my advanced versions of rescaling (including automorphism group) of this, see genuszero lines 177 and 438

intrinsic CentralPivot(cfs::SeqEnum, vls::SeqEnum, prec::RngIntElt) -> RngIntElt
  {The index of a nonzero entry of cfs whose weight vls[i] is nearest the centre of the nonzero weight range, ties to the larger modulus; 0 if every entry is zero.  An entry counts as nonzero when its modulus exceeds the largest modulus times 10^(-prec div 2).  This is the normalizing pivot of TriangleRescaleCoefficients' "Centred" mode; genus 4 uses it for the cubic too, which the rescaler does not see.}
  require #cfs eq #vls : "cfs and vls should have the same length";
  if #cfs eq 0 then
    return 0;
  end if;
  mx := Max([Abs(c) : c in cfs]);
  if mx eq 0 then
    return 0;
  end if;
  tol := mx*10^(-(prec div 2));
  nz := [i : i in [1..#cfs] | Abs(cfs[i]) gt tol];
  lo := Min([vls[i] : i in nz]);
  hi := Max([vls[i] : i in nz]);
  mid := (lo + hi)/2;
  best := nz[1];
  bd := Abs(vls[best] - mid);
  for i in nz do
    d := Abs(vls[i] - mid);
    if d lt bd or (d eq bd and Abs(cfs[i]) gt Abs(cfs[best])) then
      best := i;
      bd := d;
    end if;
  end for;
  return best;
end intrinsic;

// TODO: Make sure TriangleRescaleCoefficients works for genus one.
// Once it does, delete previous rescaling functions
intrinsic TriangleRescaleCoefficients(Gamma::GrpPSL2Tri, coeffs::SeqEnum, vals::SeqEnum : rescale_ind := 0) -> Any
  {Given a GrpPSL2Tri Gamma, and SeqEnums coeffs and vals, return the rescaling factor lamba, as well as the rescaled coefficients.  coeffs should be of the form [curve_coeffs, num_coeffs, denom_coeffs], and vals [curve_vals, num_vals, denom_vals].

   NOTE that lambda is built from num_coeffs cat denom_coeffs ALONE; the curve is merely rescaled by it afterwards.  That is deliberate and load bearing.  Lambda only has to track the torus, so it may be read from any group -- but it MUST be read from one whose weight gcd is 1, since from a group of gcd > 1 the coefficients at offsets not divisible by the gcd need a root of lambda and leave K entirely.  The map's weights are usually consecutive while the curve's need not be: the KMSV plane quartic of genus 3, for instance, is even in its second coordinate, so all of its weights are even.

   rescale_ind names, for each of curve/num/denom, the index of the coefficient to normalize that list by.  Leave it 0 -- the default -- to normalize by the FINAL entry of each list, which is what genus 1, genus 2 and the hyperelliptic path have always done and what their monomial orderings assume.  Pass [i_curve, i_num, i_denom] to name the indices explicitly, with an entry 0 meaning "the final entry of that list"; a caller whose final coefficient may vanish should pass the index of one that does not.  Pass "Centred" to normalize each list by a nonzero coefficient whose weight is nearest the CENTRE of that list's nonzero weight range (ties to the larger modulus): after the torus is undone each coefficient is (c_j/c_piv) * alpha^(w_j - w_piv) for an algebraic alpha, so its height grows like |w_j - w_piv| times the height of alpha, and a pivot at one extreme of the range roughly doubles the worst case.  Genus 3 and genus 4 use "Centred"; measured on 9T27 in each genus it brought the heights down by a third to a half and turned failed recognitions into passes.}
  g := Genus(Gamma);
  prec := Gamma`TriangleNumericalPrecision;
  eps := 10^(-prec/2);
  curve_coeffs, num_coeffs, denom_coeffs := Explode(coeffs);
  curve_vals, num_vals, denom_vals := Explode(vals);
  // which coefficient of each list to normalize that list by.  The default 0
  // reproduces the historical behaviour exactly -- the final entry of each
  // list -- so existing callers are unchanged.
  lens := [#curve_coeffs, #num_coeffs, #denom_coeffs];
  if rescale_ind cmpeq 0 then
    rinds := lens;
  elif rescale_ind cmpeq "Centred" then
    rinds := [CentralPivot(curve_coeffs, curve_vals, prec), CentralPivot(num_coeffs, num_vals, prec),
              CentralPivot(denom_coeffs, denom_vals, prec)];
    error if 0 in rinds,
        "cannot centre the pivot: one of curve, numerator, denominator is numerically zero";
    vprintf Shimura : "centred normalizing pivots at indices %o\n", rinds;
  else
    require Type(rescale_ind) eq SeqEnum and #rescale_ind eq 3 :
        "rescale_ind should be 0, \"Centred\", or a sequence [i_curve, i_num, i_denom]";
    rinds := [];
    for i in [1..3] do
      Append(~rinds, rescale_ind[i] eq 0 select lens[i] else rescale_ind[i]);
    end for;
    require &and[(rinds[i] ge 1) and (rinds[i] le lens[i]) : i in [1..3]] :
        "rescale_ind is out of range for one of curve, numerator, denominator";
  end if;
  // find valuations corresponding to nonzero coeffs
  nonzero_inds := [];
  nonzero_vals := [];
  all_coeffs := num_coeffs cat denom_coeffs;
  all_vals := num_vals cat denom_vals;
  for i in [1..#all_coeffs] do
    if Abs(all_coeffs[i]) gt eps then
      Append(~nonzero_inds, i);
      Append(~nonzero_vals, all_vals[i]);
    end if;
  end for;

  // compute rescaling factor lambda
  // TODO: deal with automorphisms...maybe dealt with: needs testing
  aut := #AutomorphismGroup(Gamma);
  error if #nonzero_vals eq 0,
      "Unable to create rescaling factor! Every numerator and denominator coefficient is numerically zero.";
  gcd, wts := Xgcd(nonzero_vals);
  // should gcd = aut? (no 09/19/17, well maybe)
  // assert gcd eq aut;
  if gcd gt 1 then
    // lambda^(1/gcd) below is determined only up to a gcd-th root of unity.
    // We do not resolve the branch here; it is settled downstream by
    // BelyiMapSanityCheck, which is what certifies the answer anyway.  (The
    // commented-out assertion just above suggests the ambiguity is the
    // automorphism group; it is left commented.)
    vprintf Shimura : "WARNING: weight gcd is %o, so lambda^(1/%o) is determined only up to a %o-th root of unity; the branch is resolved downstream by BelyiMapSanityCheck.\n", gcd, gcd, gcd;
  end if;
  vprintf Shimura : "nonzero_inds = %o\ngcd = %o\nwts = %o\n", nonzero_inds, gcd, wts;
  wts_sum := &+[wts[i] : i in [1..#wts]];
  lambda := &*[all_coeffs[nonzero_inds[i]]^wts[i] : i in [1..#nonzero_inds]];
  if wts_sum ne 0 then
    if 0 in nonzero_vals then
      ind := Index(nonzero_vals,0);
      lambda := lambda*all_coeffs[nonzero_inds[ind]]^(-wts_sum);
      wts[ind] +:= -wts_sum; // FIXME maybe -- no test currently reaches this line
    else
      // lambda is read from num cat denom alone, so it is one of THOSE two
      // that lacks a weight-zero coefficient; the curve is not consulted.
      // Affine input supplies it as the constant term.
      error Sprintf("Unable to create rescaling factor! No nonzero coefficient of weight zero in the numerator or the denominator (the curve is not consulted for lambda).  Numerator weights: %o.  Denominator weights: %o.", num_vals, denom_vals);
    end if;
  end if;
  lambda := lambda^(1/gcd);
  // lambda := lambda^(1/aut);
  lambda := 1/lambda;

  // now rescale coefficients using lambda
  for i in [1..#curve_coeffs] do
    curve_coeffs[i] := curve_coeffs[i]*(lambda^curve_vals[i]);
  end for;
  curve_pivot := curve_coeffs[rinds[1]];
  error if curve_pivot eq 0,
      Sprintf("cannot normalize the curve by coefficient %o: it is zero (pass rescale_ind to name another)", rinds[1]);
  curve_coeffs := [curve_coeffs[i]/curve_pivot : i in [1..#curve_coeffs]];
  for i in [1..#num_coeffs] do
    num_coeffs[i] := num_coeffs[i]*(lambda^num_vals[i]);
  end for;
  for i in [1..#denom_coeffs] do
    denom_coeffs[i] := denom_coeffs[i]*(lambda^denom_vals[i]);
  end for;
  lc_num := num_coeffs[rinds[2]];
  lc_den := denom_coeffs[rinds[3]];
  error if lc_num eq 0,
      Sprintf("cannot normalize the numerator by coefficient %o: it is zero (pass rescale_ind to name another)", rinds[2]);
  error if lc_den eq 0,
      Sprintf("cannot normalize the denominator by coefficient %o: it is zero (pass rescale_ind to name another)", rinds[3]);
  // lc = lc_num/lc_den and the two lists are divided by lc_num and lc_den, so
  // lc*(num/denom) is the original ratio whatever indices were chosen
  lc := lc_num/lc_den;
  for i in [1..#denom_coeffs] do
    denom_coeffs[i] := denom_coeffs[i]/lc_den;
  end for;
  for i in [1..#num_coeffs] do
    num_coeffs[i] := num_coeffs[i]/lc_num;
  end for;
  // assign attribute TriangleNewtonRescalingData for NewtonGenusOne
  Gamma`TriangleNewtonRescalingData := [* gcd, wts, nonzero_inds, nonzero_vals *];
  // assign data to Gamma
  Gamma`TriangleNumericalCurveCoefficients := curve_coeffs;
  Gamma`TriangleNumericalBelyiMapLeadingCoefficient := lc;
  Gamma`TriangleNumericalBelyiMapNumeratorCoefficients := num_coeffs;
  Gamma`TriangleNumericalBelyiMapDenominatorCoefficients := denom_coeffs;
  vprintf Shimura : "Rescaled coefficients computed and assigned.\n";
  return lambda, curve_coeffs, lc, num_coeffs, denom_coeffs, nonzero_inds, wts;
end intrinsic;

// TODO: Make work for genus 2, at least
intrinsic TriangleRecordCoefficients(Gammas::SeqEnum[GrpPSL2Tri] : prec := 40, PowserAl := "Arnoldi") -> Any
  {Given a sequence of triangle subgroups (GrpPSL2Tris), write FldComElt invariants and coefficients for the curve and BelyiMap to the objects.}
  // should we return a bool?
  // check if numerical data already exists for this object
  assert #Gammas gt 0;
  already_computed := 1;
  for Gamma in Gammas do
    if assigned Gamma`TriangleNumericalPrecision and assigned Gamma`TriangleNumericalCurveInvariants and assigned Gamma`TriangleNumericalCurveCoefficients and assigned Gamma`TriangleNumericalBelyiMapLeadingCoefficient and assigned Gamma`TriangleNumericalBelyiMapNumeratorCoefficients and assigned Gamma`TriangleNumericalBelyiMapDenominatorCoefficients then
      old_prec := Precision(Parent(Gamma`TriangleNumericalBelyiMapNumeratorCoefficients[1]));
      if old_prec ge prec then
        already_computed *:= 1;
      else
        already_computed *:= 0;
      end if;
    else
      already_computed *:= 0;
    end if;
  end for;
  if already_computed eq 1 then
    return Sprintf("Numerical data already computed at precision greater than or equal to %o for each Gamma.\n", prec);
  end if;
  // need an initial Gamma for rescale_index
  // then loop over other Gamma in Gammas
  initial_Gamma := Gammas[1];
  genus := Genus(initial_Gamma);
  if genus eq 1 then
    _ := UnitDisc(initial_Gamma : Precision := prec);
    Sk := PowerSeriesBasis(initial_Gamma, 2 : prec := prec, Al := PowserAl);
    CC<I> := BaseRing(Parent(Sk[1][1]));
    DDs := initial_Gamma`TriangleDDs;
    // get numerical data for initial_Gamma
    _, rescale_ind, num_bool := TriangleGenusOneNumericalBelyiMap(Sk[1], initial_Gamma);
    if #Gammas ge 2 then
      for j in [2..#Gammas] do
        Gamma := Gammas[j];
        _:= UnitDisc(Gamma : Precision := prec);
        Sk := PowerSeriesBasis(Gamma, 2 : prec := prec, Al := PowserAl);
        _, i_j, num_bool_j := TriangleGenusOneNumericalBelyiMap(Sk[1],Gamma : rescale_ind := rescale_ind, num_bool := num_bool);
        //need to make sure same indices of coefficients are used in computing lambda!
        if i_j ne rescale_ind or num_bool_j ne num_bool then
          error "Inconsistent rescaling index!\n";
        end if;
      end for;
    end if;
  elif genus eq 2 then
    _ := UnitDisc(initial_Gamma : Precision := prec);
    Sk := PowerSeriesBasis(initial_Gamma, 2 : prec := prec, Al := PowserAl);
    CC<I> := BaseRing(Parent(Sk[1][1]));
    DDs := initial_Gamma`TriangleDDs;
    // get numerical data for initial_Gamma
    TriangleHyperellipticNumericalCoefficients(Sk, initial_Gamma);
    if #Gammas ge 2 then
      for j in [2..#Gammas] do
        Gamma := Gammas[j];
        _ := UnitDisc(Gamma : Precision := prec);
        Sk := PowerSeriesBasis(Gamma, 2 : prec := prec, Al := PowserAl);
        TriangleHyperellipticNumericalCoefficients(Sk, Gamma);
      end for;
    end if;
  else
    error "Not implemented for genus greater than 2.";
  end if;
  return "Numerical data for given triangle subgroups computed and assigned.";
end intrinsic;

intrinsic TriangleRecordCoefficients(sigmas::SeqEnum[SeqEnum[GrpPermElt]] : prec := 40, PowserAl := "Arnoldi") -> Any
  {Given a sequence of permutation triples, write FldComElt invariants and coefficients for the curve and BelyiMap to the objects.}
  Gammas := [TriangleSubgroup(sigma) : sigma in sigmas];
  TriangleRecordCoefficients(Gammas : prec := prec, PowserAl := PowserAl);
  return Gammas;
end intrinsic;

intrinsic TriangleRootMatcher5000(z::FldComElt, fact_list::SeqEnum) -> Any
  {Given a complex number z, thought to be a root of one of polynomials in fact_list
    (in the format output by Factorization()), identify which polynomial it satisfies.
    Returns the polynomial f, the error err, an optimized representation of the number field
    defined by f, and the embedding data given by a place v and boolean conj.}

  CC<I> := Parent(z);
  prec := Precision(z);
  eps := 10^(-prec/2);
  R<x> := PolynomialRing(Rationals());

  for i in [1..#fact_list] do
    f := fact_list[i][1];
    if Abs(Evaluate(f,z)) lt eps then //machine zero
      f_0 := f;
      err := Abs(Evaluate(f,z));
        if Degree(f) eq 1 then //degree 1, i.e., K is QQ
          K := RationalsAsNumberField();
          Kop := K;
          v := InfinitePlaces(Kop)[1];
          zop := Coefficient(f, 0);
          conj := false;
        else //degree > 1
          K<zK> := NumberField(f);
          ps, foobar := TrialDivision(Discriminant(K));
          if foobar ne 1 and not IsSquare(foobar) then
            error "Discriminant doesn't jive...try a higher precision";
          end if;
          if foobar eq 1 then
            vprintf Shimura : "  ...number field found, with ps = %o and foobar = 1\n", ps;
          else
            vprintf Shimura : "  ...number field found, with ps = %o and sqrt(foobar) = %o\n", ps, Round(Sqrt(CC!foobar));
          end if;
          vprintf Shimura : "  ...%o\n", K;
          vprint Shimura : "  ...Optimizing";
          Kop, iotaop := OptimizedRepresentation(K : Ramification := [p[1] : p in ps]);
          //Kop, iotaop := OptimizedRepresentation(K : PartialFactorisation);
          vprintf Shimura: "Optimized field is %o", Kop; //printing
          zop := iotaop(zK);
          vprint Shimura : "  ...successfully optimized, now finding complex embedding\n";
          minv, vind := Min([Abs(z-Evaluate(zop,v : Precision := Precision(CC))) : v in InfinitePlaces(Kop)]);
          if minv gt eps then
            // Need complex conjugate
            minv, vind := Min([Abs(Conjugate(z)-Evaluate(zop,v : Precision := Precision(CC))) : v in InfinitePlaces(Kop)]);
            conj := true;
          else
            conj := false;
          end if;
          if minv gt eps then
            error "Large error after embedding...something is fishy\n";
          end if;
          vprintf Shimura : "Error from embedding is %o\n", minv;
          v := InfinitePlaces(Kop)[vind];
        end if;
    end if;
  end for;
  zopCC := Evaluate(zop, v : Precision := Precision(CC));
  if conj then
    zopCC := ComplexConjugate(zopCC);
  end if;
  return f_0, err, Kop, v, conj, zopCC;
end intrinsic;

// should this really be an intrinsic?  Maybe just a function...
// maybe modify to make it compute the eps from the coefficients...
intrinsic GaloisMinPoly(L::SeqEnum[FldComElt], eps::FldReElt) -> Any
  {Given a list of Galois conjugate complex numbers returns their (possibly) reducible "minpoly".}
  CC<I> := Parent(L[1]);
  CCx<x> := PolynomialRing(CC);
  f := &*[x-a : a in L];
  QQ := Rationals();
  QQx<x> := PolynomialRing(QQ);
  cs := Coefficients(f);
  cs := [Re(c) : c in cs];
  cs_QQ := [];
  for c in cs do
    if Abs(c) lt eps then //machine zero
      c_QQ := QQ!0;
    else
      //c_QQ := Roots(PowerRelation(c,1),QQ)[1][1];
      lin := LinearRelation([CC!c, 1]);
      c_QQ := -lin[2]/lin[1];
    end if;
    Append(~cs_QQ,c_QQ);
  end for;
  f_QQ := QQx!cs_QQ;
  return f_QQ, cs;
end intrinsic;

intrinsic TriangleLengthSort(Gammas::SeqEnum[GrpPSL2Tri]) -> Any
  {}
  assert #Gammas gt 0;
  genus := Genus(Gammas[1]);
  curve_invs := [];
  curve_coeffs := [];
  denom_coeffs := [];
  num_coeffs := [];
  leading_coeffs := [];
  lengths := [];
  for Gamma in Gammas do
    Append(~curve_coeffs, Gamma`TriangleNumericalCurveCoefficients);
    Append(~leading_coeffs, Gamma`TriangleNumericalBelyiMapLeadingCoefficient);
    Append(~num_coeffs, Gamma`TriangleNumericalBelyiMapNumeratorCoefficients);
    Append(~denom_coeffs, Gamma`TriangleNumericalBelyiMapDenominatorCoefficients);
    Append(~lengths, [#Gamma`TriangleNumericalBelyiMapNumeratorCoefficients, #Gamma`TriangleNumericalBelyiMapDenominatorCoefficients]);
  end for;
  leading_coeffs_new := [[el] : el in leading_coeffs]; //should probably actually fix this to make treatment uniform, rather than this band-aid
  // have to break up by the lengths of the coeffs, otherwise get index out of range errors
  // see d5g2 size 3 example for instance of this
  lengths := SetToSequence(SequenceToSet(lengths));
  Gammas_sorted := [[] : j in [1..#lengths]];
  if genus eq 1 then
    coeffs := [*curve_invs, curve_coeffs, denom_coeffs, num_coeffs, leading_coeffs_new*];
  else
    coeffs := [*curve_coeffs, denom_coeffs, num_coeffs, leading_coeffs_new*];
  end if;
  coeffs_sorted := [[[] : i in [1..#coeffs]] : j in [1..#lengths]];
  for i in [1..#denom_coeffs] do
    for j in [1..#lengths] do
      if [#num_coeffs[i], #denom_coeffs[i]] eq lengths[j] then
        Append(~Gammas_sorted[j], Gammas[i]);
        for k in [1..#coeffs] do
          Append(~coeffs_sorted[j][k], coeffs[k][i]);
        end for;
      end if;
    end for;
  end for;
  return coeffs_sorted, Gammas_sorted;
end intrinsic;

intrinsic TriangleRecognizeCoefficients(Gammas::SeqEnum[GrpPSL2Tri] : ExactAl := "GaloisOrbits", DegreeBound := 0) -> Any
  {Given a sequence of triangle subgroups with all the numerical stuff computed, to each one assign a number field, coefficients of the curve and Belyi map as elements of this number field. ExactAl specifies algorithm by which coefficients are recognized. Options are GaloisOrbits (requires the sequence of Gammas to be closed under the action of Galois) and AlgebraicNumbers which attempts to recognize the algebraic coefficients directly over a number field with degree bounded by DegreeBound, if given (otherwise taken to be the size of the pointed passport for Gamma).}
  assert #Gammas gt 0;
  genus := Genus(Gammas[1]);
  curve_invs := [];
  curve_coeffs := [];
  denom_coeffs := [];
  num_coeffs := [];
  leading_coeffs := [];
  lengths := [];
  for Gamma in Gammas do
    Append(~curve_coeffs, Gamma`TriangleNumericalCurveCoefficients);
    Append(~leading_coeffs, Gamma`TriangleNumericalBelyiMapLeadingCoefficient);
    Append(~num_coeffs, Gamma`TriangleNumericalBelyiMapNumeratorCoefficients);
    Append(~denom_coeffs, Gamma`TriangleNumericalBelyiMapDenominatorCoefficients);
    Append(~lengths, [#Gamma`TriangleNumericalBelyiMapNumeratorCoefficients, #Gamma`TriangleNumericalBelyiMapDenominatorCoefficients]);
  end for;
  leading_coeffs_new := [[el] : el in leading_coeffs]; //should probably actually fix this to make treatment uniform, rather than this band-aid

  // have to break up by the lengths of the coeffs, otherwise get index out of range errors
  // see d5g2 size 3 example for instance of this
  lengths := SetToSequence(SequenceToSet(lengths));
  if genus eq 1 then
    for Gamma in Gammas do
      Append(~curve_invs, [Gamma`TriangleNumericalCurveInvariants]);
    end for;
    coeffs := [*curve_invs, curve_coeffs, denom_coeffs, num_coeffs, leading_coeffs_new*];
    if ExactAl eq "GaloisOrbits" then
      // make minimal polynomials
      prec := Precision(Parent(denom_coeffs[1][1]));
      eps := 10^(-prec/2); // this is machine zero
      CC<I> := ComplexField(prec);
      R<x> := PolynomialRing(CC);
      invs_polys_QQ := [];
      poly := GaloisMinPoly([curve_invs[i][1] : i in [1..#curve_invs]],eps);
      Append(~invs_polys_QQ, poly);
      // Could probably just write a for-loop to do these...
      curve_polys_QQ := [];
      for j in [1,2] do
        poly := GaloisMinPoly([curve_coeffs[i][j] : i in [1..#curve_coeffs]],eps);
        Append(~curve_polys_QQ, poly);
      end for;
      leading_poly_QQ  := GaloisMinPoly(leading_coeffs,eps);
      denom_polys_QQ := [];
      for j in [1..#denom_coeffs[1]] do
        poly := GaloisMinPoly([denom_coeffs[i][j] : i in [1..#denom_coeffs]],eps);
        Append(~denom_polys_QQ, poly);
      end for;
      num_polys_QQ := [];
      for j in [1..#num_coeffs[1]] do
        poly := GaloisMinPoly([num_coeffs[i][j] : i in [1..#num_coeffs]],eps);
        Append(~num_polys_QQ, poly);
      end for;
      polys_QQ := [invs_polys_QQ, curve_polys_QQ, denom_polys_QQ, num_polys_QQ, [leading_poly_QQ]];
      vprint Shimura : polys_QQ;
      
      // factor
      facts := [];
      for i in {1..#polys_QQ} do
        facts_i := [];
        for f in polys_QQ[i] do
          Append(~facts_i, Factorization(f));
        end for;
        Append(~facts, facts_i);
      end for;
      vprint Shimura : facts;

      // Find polynomial with largest irreducible factors
      vprint Shimura : "Finding polynomial with largest irrreducible factors";
      big_i := 1;
      big_j := 1;
      for i in [1..#coeffs] do
        for j in [1..#facts[i]] do
          if [Degree(facts[i][j][k][1]) : k in [1..#facts[i][j]]] gt [Degree(facts[big_i][big_j][k][1]) : k in [1..#facts[big_i][big_j]]] then
            big_i := i;
            big_j := j;
          end if;
        end for;
      end for;
      fact_list := facts[big_i][big_j];
      vprintf Shimura : "Factorization with largest irreducible factors is %o\n", fact_list;
      c_list := coeffs[big_i];
      gens := [el[big_j] : el in c_list];

      vprint Shimura : "Finding number fields...";
      field_data := [];
      for i in [1..#gens] do
        f, err, K, v, conj, zop := TriangleRootMatcher5000(gens[i], fact_list);
        vprintf Shimura : "%o satisfies %o with an error of %o\n", gens[i], f, err;
        vprintf Shimura : "Number field found is %o\n", K;
        Gamma := Gammas[i];
        Gamma`TriangleKMinPoly := f;
        Gamma`TriangleK := K;
        Gamma`TriangleKv := v;
        Gamma`TriangleKIsConjugated := conj;
        Gamma`TriangleKNumericalGenerator := zop;
        Append(~field_data, [* K, v, conj, zop *]);
      end for;

      vprintf Shimura: "Recognizing rest of the coefficients...\n";

      coeffs_K := [*[*[] : i in [1..#field_data]*] : j in [1..5]*];
      // order of coeffs_K is curve_invs, curve_coeffs, denom_coeffs, num_coeffs, leading_coeffs_new
      for m in [1..5] do // m is curve_invs, curve_coeffs, etc.
        polys_QQ_m := polys_QQ[m];
        for k in [1..#polys_QQ_m] do // k is which coeff of given poly over rationals
          f := polys_QQ_m[k];
          for i in [1..#field_data] do // i is which field
            K := field_data[i][1];
            v := field_data[i][2];
            conj := field_data[i][3];
            roots := Roots(f,K);
            for j in [1..#roots] do
              r := roots[j][1];
              ev := Evaluate(r,v);
              if conj then
                ev := ComplexConjugate(ev);
              end if;
              if Abs(ev - coeffs[m][i][k]) lt eps/2 then //machine zero
                Append(~coeffs_K[m][i],r);
              end if;
            end for;
          end for;
        end for;
      end for;
      //order of coeffs_K is curve_invs, curve_coeffs, denom_coeffs, num_coeffs, leading_coeffs_new
      for i := 1 to #Gammas do
        Gamma := Gammas[i];
        Gamma`TriangleExactCurveInvariants := coeffs_K[1][i];
        Gamma`TriangleExactCurveCoefficients := coeffs_K[2][i];
        Gamma`TriangleExactBelyiMapLeadingCoefficient := coeffs_K[5][i][1]; // this should be a number
        Gamma`TriangleExactBelyiMapNumeratorCoefficients := coeffs_K[4][i];
        Gamma`TriangleExactBelyiMapDenominatorCoefficients := coeffs_K[3][i];
      end for;
    elif ExactAl eq "AlgebraicNumbers" then
      for i := 1 to #Gammas do
        TriangleRecognizeAlgebraicCoefficients(Gammas[i] : DegreeBound := DegreeBound);
      end for;
    end if;
  elif genus eq 2 then
    coeffs := [*curve_coeffs, denom_coeffs, num_coeffs, leading_coeffs_new*];
    if ExactAl eq "GaloisOrbits" then
      coeffs_sorted, Gammas_sorted := TriangleLengthSort(Gammas);
      assert #coeffs_sorted eq #Gammas_sorted;
      for k := 1 to #coeffs_sorted do
        curve_coeffs_k := coeffs_sorted[k][1];
        denom_coeffs_k := coeffs_sorted[k][2];
        num_coeffs_k := coeffs_sorted[k][3];
        leading_coeffs_new_k := coeffs_sorted[k][4];
        leading_coeffs_k := [el[1] : el in leading_coeffs_new_k];
        Gammas_k := Gammas_sorted[k];
        // make minimal polynomials
        prec := Precision(Parent(curve_coeffs_k[1][1]));
        eps := 10^(-prec/2); // this is machine zero
        CC<I> := ComplexField(prec);
        R<x> := PolynomialRing(CC);
        // Could probably just write a for loop to do these...
        curve_polys_QQ := [];
        for j in [1..#curve_coeffs_k[1]] do
          poly := GaloisMinPoly([curve_coeffs_k[i][j] : i in [1..#curve_coeffs_k]],eps);
          Append(~curve_polys_QQ, poly);
        end for;
        leading_poly_QQ  := GaloisMinPoly(leading_coeffs_k,eps);
        denom_polys_QQ := [];
        for j in [1..#denom_coeffs_k[1]] do
          poly := GaloisMinPoly([denom_coeffs_k[i][j] : i in [1..#denom_coeffs_k]],eps);
          Append(~denom_polys_QQ, poly);
        end for;
        num_polys_QQ := [];
        for j in [1..#num_coeffs_k[1]] do
          poly := GaloisMinPoly([num_coeffs_k[i][j] : i in [1..#num_coeffs_k]],eps);
          Append(~num_polys_QQ, poly);
        end for;
        polys_QQ := [curve_polys_QQ, denom_polys_QQ, num_polys_QQ, [leading_poly_QQ]];
        vprint Shimura : polys_QQ;
        
        // factor
        facts := [];
        for i in {1..#polys_QQ} do
          facts_i := [];
          for f in polys_QQ[i] do
            Append(~facts_i, Factorization(f));
          end for;
          Append(~facts, facts_i);
        end for;
        vprint Shimura : facts;

        // Find polynomial with largest irreducible factors
        vprint Shimura : "Finding polynomial with largest irrreducible factors";
        big_i := 1;
        big_j := 1;
        for i in [1..#polys_QQ] do
          for j in [1..#facts[i]] do
            if [Degree(facts[i][j][r][1]) : r in [1..#facts[i][j]]] gt [Degree(facts[big_i][big_j][r][1]) : r in [1..#facts[big_i][big_j]]] then
              big_i := i;
              big_j := j;
            end if;
          end for;
        end for;
        fact_list := facts[big_i][big_j];
        print fact_list;
        vprintf Shimura : "Factorization with largest irreducible factors is %o\n", fact_list;
        c_list := coeffs_sorted[k][big_i];
        // printf "big_i = %o, big_j = %o\n", big_i, big_j;
        gens := [el[big_j] : el in c_list];

        vprint Shimura : "Finding number fields...";
        field_data := [];
        for i in [1..#gens] do
          f, err, K, v, conj, zop := TriangleRootMatcher5000(gens[i], fact_list);
          vprintf Shimura : "%o satisfies %o with an error of %o\n", gens[i], f, err;
          vprintf Shimura : "Number field found is %o\n", K;
          Gamma := Gammas_k[i];
          Gamma`TriangleKMinPoly := f;
          Gamma`TriangleK := K;
          Gamma`TriangleKv := v;
          Gamma`TriangleKIsConjugated := conj;
          Gamma`TriangleKNumericalGenerator := zop;
          Append(~field_data, [* K, v, conj, zop *]);
        end for;

        vprintf Shimura: "Recognizing rest of the coefficients...\n";

        coeffs_K := [*[*[] : i in [1..#field_data]*] : j in [1..4]*];
        // order of coeffs_K is curve_coeffs, denom_coeffs, num_coeffs, leading_coeffs_new
        for m in [1..4] do // m is curve_coeffs, etc.
          polys_QQ_m := polys_QQ[m];
          for el in [1..#polys_QQ_m] do // k is which coeff of given poly over rationals
            f := polys_QQ_m[el];
            for i in [1..#field_data] do // i is which field
              K := field_data[i][1];
              v := field_data[i][2];
              conj := field_data[i][3];
              roots := Roots(f,K);
              // print roots;
              for j in [1..#roots] do
                r := roots[j][1];
                ev := Evaluate(r,v);
                if conj then
                  ev := ComplexConjugate(ev);
                end if;
                if Abs(ev - coeffs_sorted[k][m][i][el]) lt eps/2 then //machine zero
                  Append(~coeffs_K[m][i],r);
                end if;
              end for;
            end for;
          end for;
        end for;
        //order of coeffs_K is curve_coeffs, denom_coeffs, num_coeffs, leading_coeffs_new
        // FIXME genus 2
        for i := 1 to #Gammas_k do
          Gamma := Gammas_k[i];
          Gamma`TriangleExactCurveCoefficients := coeffs_K[1][i];
          Gamma`TriangleExactBelyiMapLeadingCoefficient := coeffs_K[4][i][1]; // changed by MM 12/01/17...coefficient should be a number not a seqenum...maybe
          Gamma`TriangleExactBelyiMapNumeratorCoefficients := coeffs_K[3][i];
          Gamma`TriangleExactBelyiMapDenominatorCoefficients := coeffs_K[2][i];
        end for;
      end for;
    elif ExactAl eq "AlgebraicNumbers" then
      for i := 1 to #Gammas do
        TriangleRecognizeAlgebraicCoefficients(Gammas[i] : DegreeBound := DegreeBound);
      end for;
    end if;
  else
    error "Not implemented for genus gt 2";
  end if;
  return "Exact curve and Belyi map data computed and assigned";
end intrinsic;

intrinsic TriangleRecognizeAlgebraicCoefficients(Gamma::GrpPSL2Tri : DegreeBound := 0) -> Any
  {Given a triangle subgroup with all the numerical stuff computed, assign it a number field, coefficients of the curve and Belyi map as elements of this number field.}
  if Genus(Gamma) eq 1 then
    vprint Shimura : "Looking for coefficient to recognize number field...";
    Kbool := false;
    j := Gamma`TriangleNumericalCurveInvariants;
    c4, c6 := Explode(Gamma`TriangleNumericalCurveCoefficients);
    u := Gamma`TriangleNumericalBelyiMapLeadingCoefficient;
    denom_coeffs := Gamma`TriangleNumericalBelyiMapDenominatorCoefficients;
    num_coeffs := Gamma`TriangleNumericalBelyiMapNumeratorCoefficients;
    cfs := [j, c4, c6] cat denom_coeffs cat num_coeffs;
    cfs_ind := 0;
    vprintf Shimura : "coefficients are %o\n", cfs;
    if DegreeBound eq 0 then
      sigma := Gamma`TriangleSigma;
      DegreeBound := #PassportRepresentatives(sigma : Pointed := true);
    end if;
    while not Kbool and cfs_ind lt #cfs do
      cfs_ind +:= 1;
      vprintf Shimura: "coefficients are %o\n", cfs_ind;
      Kbool, K, v, conj, uCC := MakeK(cfs[cfs_ind], DegreeBound);
    end while;
    if not Kbool then
      error "Unable to create number field!";
    end if;
    vprint Shimura : "... found!", K;
    vprint Shimura : "Recognizing coefficients...";
    Gamma`TriangleK := K;
    Gamma`TriangleKv := v;
    Gamma`TriangleKIsConjugated := conj;
    Gamma`TriangleKNumericalGenerator := uCC;
    j_K := RecognizeOverK(j,K,v,conj);
    c4_K := RecognizeOverK(c4,K,v,conj);
    c6_K := RecognizeOverK(c6,K,v,conj);
    Gamma`TriangleExactCurveInvariants := [j_K];
    Gamma`TriangleExactCurveCoefficients := [c4_K, c6_K];
    denom_coeffs := [RecognizeOverK(el,K,v,conj) : el in denom_coeffs];
    num_coeffs := [RecognizeOverK(el,K,v,conj) : el in num_coeffs];
    u := RecognizeOverK(u,K,v,conj);
    Gamma`TriangleExactBelyiMapLeadingCoefficient := u;
    Gamma`TriangleExactBelyiMapNumeratorCoefficients := num_coeffs;
    Gamma`TriangleExactBelyiMapDenominatorCoefficients := denom_coeffs;
    return Sprintf("Algebraic coefficients recognized and assigned for %o\n", Gamma);
  // the body below is generic: it recognizes curve_coeffs cat denom_coeffs cat
  // num_coeffs without caring what they mean, so the genus 3 non-hyperelliptic
  // case (genus3nonhyperelliptic.m) uses it unchanged.  Magma errors on
  // READING an unassigned attribute, so each attribute is guarded -- for
  // genus 2 the first disjunct short circuits before either is touched.
  elif ((Genus(Gamma) eq 2)
        or (assigned Gamma`TriangleIsHyperelliptic and Gamma`TriangleIsHyperelliptic)
        or (assigned Gamma`TriangleIsGenus3NonHyperelliptic and Gamma`TriangleIsGenus3NonHyperelliptic)
        or (assigned Gamma`TriangleIsGenus4Canonical and Gamma`TriangleIsGenus4Canonical)) then
    vprint Shimura : "Looking for coefficient to recognize number field...";
    Kbool := false;
    curve_coeffs := Gamma`TriangleNumericalCurveCoefficients;
    u := Gamma`TriangleNumericalBelyiMapLeadingCoefficient;
    denom_coeffs := Gamma`TriangleNumericalBelyiMapDenominatorCoefficients;
    num_coeffs := Gamma`TriangleNumericalBelyiMapNumeratorCoefficients;
    cfs := curve_coeffs cat denom_coeffs cat num_coeffs;
    vprintf Shimura : "coefficients are %o\n", cfs;
    if DegreeBound eq 0 then
      sigma := Gamma`TriangleSigma;
      DegreeBound := #PassportRepresentatives(sigma : Pointed := true);
    end if;
    CCu := Parent(cfs[1]);
    precu := Precision(CCu);
    eps := 10^(-precu/2);

    /*
      Relations and gates.  Every relation below is found by LLL on an
      explicit lattice, rows [e_i | round(10^q Re x_i) | round(10^q Im x_i)],
      scaled to q = 4p/5 digits (what the coefficients actually carry), and
      accepted only when its height is two digits below the phony floor
      10^(q/n) of a relation among n numbers.  The measurements behind q,
      the floor and the gate, and why Magma's PowerRelation/LinearRelation
      are not used, are in Doc/adr-genus4.md, section 4, "Calibration".
    */
    qscale := Floor(4*precu/5);
    floordigits := func<n | qscale/n>;
    Gate := func<m | 10^(floordigits(m+1) - 2)>;

    // Relation: an integer relation among the complex numbers xs.  Returns
    // the relation, its height, and the residual |sum c_i x_i|.
    Relation := function(xs);
      n := #xs;
      sc := 10^qscale;
      M := ZeroMatrix(Integers(), n, n+2);
      for i in [1..n] do
        M[i,i] := 1;
        M[i,n+1] := Round(sc*Real(xs[i]));
        M[i,n+2] := Round(sc*Imaginary(xs[i]));
      end for;
      L := LLL(M);
      c := [L[1,i] : i in [1..n]];
      return c, Max([Abs(a) : a in c]), Abs(&+[c[i]*xs[i] : i in [1..n]]);
    end function;

    /*
      Propose: MakeK's proposal step (minimal polynomial of z of degree
      exactly m, irreducible, same MakeKFromPoly tail) with an optional
      height gate, plus a HINT when the relation has a single irreducible
      factor of lower degree: a degree to try next, never a field to accept.
      Returns bl, K, v, conj, uCC, hint.
    */
    ZZx := PolynomialRing(Integers());
    Propose := function(z, m, gate);
      c, ht, res := Relation([z^k : k in [0..m]]);
      u_pol := ZZx!c;
      u_pol := u_pol div GCD(c);
      if Degree(u_pol) ne m or not IsIrreducible(u_pol) then
        hint := 0;
        if Degree(u_pol) gt 1 then
          fac := [f[1] : f in Factorization(u_pol) | Degree(f[1]) gt 1];
          vprint Shimura : "  ...coefficient not degree m, looked like degree", [<Degree(c[1]),c[2]> : c in Factorization(u_pol)];
          if #fac eq 1 and Degree(fac[1]) lt m then
            hint := Degree(fac[1]);
          end if;
        end if;
        return false, 0, 0, false, 0, hint;
      end if;
      if gate gt 0 and ht gt gate then
        vprintf Shimura : "  ...degree %o relation of height %o exceeds the gate %o: phony\n", m, ht, RealField(3)!gate;
        return false, 0, 0, false, 0, 0;
      end if;
      bl, K, v, conj, uCC := MakeKFromPoly(z, u_pol);
      if not bl then
        return false, 0, 0, false, 0, 0;
      end if;
      return bl, K, v, conj, uCC, 0;
    end function;

    /*
      FitOverK: recognize every number in xs over an O_K basis.  Returns
      ok, bad, rec: the recognized list, or the index of the first number
      that failed the height gate (when gated) or the residual check.
      Ungated it replaces the scalar RecognizeOverK, whose reduced-precision
      LinearRelation misrecognized a leading coefficient (ADR section 4).
    */
    FitOverK := function(xs, K, v, conj, gated);
      m := Degree(K);
      ZK := Integers(K);
      ZKbCC := [CCu!Evaluate(b, v : Precision := precu) : b in Basis(ZK)];
      if conj then
        ZKbCC := [Conjugate(b) : b in ZKbCC];
      end if;
      rec := [K | ];
      for i in [1..#xs] do
        z := xs[i];
        if Abs(z) lt eps then
          Append(~rec, K!0);
          continue;
        end if;
        lin, ht, res := Relation(ZKbCC cat [-z]);
        if lin[m+1] eq 0 then
          vprintf Shimura : "  ...coefficient %o: no relation over K\n", i;
          return false, i, rec;
        end if;
        if gated and ht gt Gate(m) then
          vprintf Shimura : "  ...coefficient %o: relation of height %o exceeds the gate %o\n", i, ht, RealField(3)!Gate(m);
          return false, i, rec;
        end if;
        zK := K!((ZK!lin[1..m])/lin[m+1]);
        zv := CCu!Evaluate(zK, v : Precision := precu);
        if conj then
          zv := Conjugate(zv);
        end if;
        if Abs(zv - z) gt eps*Max(1, Abs(z)) then
          vprintf Shimura : "  ...coefficient %o: fits only to %o\n", i, RealField(3)!Abs(zv - z);
          return false, i, rec;
        end if;
        vprintf Shimura, 2 : "  ...coefficient %o fits with height %o (gate %o), residual %o\n", i, ht, RealField(3)!Gate(m), RealField(3)!res;
        Append(~rec, zK);
      end for;
      return true, 0, rec;
    end function;

    // 0. the given bound, ungated: one irreducible relation of degree
    //    DegreeBound certifies the field by itself (only Q, at the bottom of
    //    the subfield lattice, needs every coefficient).  Hints from rejected
    //    relations are kept for the fallback.
    rec := [];
    hints := [];
    cfs_ind := 0;
    while not Kbool and cfs_ind lt #cfs do
      cfs_ind +:= 1;
      vprintf Shimura: "coefficients are %o\n", cfs_ind;
      if DegreeBound eq 1 then
        Kbool, K, v, conj, uCC := MakeK(cfs[cfs_ind], 1);
      else
        Kbool, K, v, conj, uCC, hint := Propose(cfs[cfs_ind], DegreeBound, 0);
        if hint ge 2 and hint lt DegreeBound and not hint in hints then
          vprintf Shimura : "  ...hint: coefficient %o looks like degree %o\n", cfs_ind, hint;
          Append(~hints, hint);
        end if;
      end if;
    end while;
    // The passport size bounds the degree of the field of definition but
    // need not equal it (members related by permuting 0, 1, oo rather than
    // by Galois are each over a smaller field), so before giving up retry
    // with smaller bounds: Q first, then the hinted degrees, then the rest
    // ascending, every candidate VERIFIED on all of cfs before acceptance.
    // Accepting on a sample was the bug (Doc/SPEC-degreebound-fallback.md).
    if not Kbool and DegreeBound gt 1 then
      vprintf Shimura : "MakeK found no field of degree %o; retrying with smaller degree bounds\n", DegreeBound;
      // 1. Q, gated totally: every coefficient real (decisive for an
      //    imaginary field) and every coefficient fitting at degree 1 under
      //    the gate.  MakeK(z, 1) accepts Q unconditionally, so it is called
      //    only after this test.
      allreal := true;
      for z in cfs do
        if Abs(z) ge eps and Abs(Imaginary(z)) gt eps*Max(RealField(precu)!1, Abs(z)) then
          allreal := false;
          break;
        end if;
      end for;
      if allreal then
        Kbool, K, v, conj, uCC := MakeK(cfs[1], 1);
        ok, bad, rec := FitOverK(cfs, K, v, conj, true);
        if ok then
          vprintf Shimura : "every coefficient is real and fits over QQ, so K = QQ\n";
        else
          vprintf Shimura : "coefficient %o does not fit over QQ\n", bad;
          Kbool := false;
          rec := [];
        end if;
      else
        vprintf Shimura : "not every coefficient is real, so K is not QQ\n";
      end if;
      // 2. ascend through the proper degrees, hinted ones first: propose
      //    with the gate, verify on all of cfs.  Any failure rejects the
      //    candidate and the ascent goes on (a candidate fitting the head
      //    and failing the tail may be a proper subfield, which looks like a
      //    precision failure; ADR section 4); exhausting every degree
      //    reports the best partial fit.
      degs := [m : m in hints | m ge 2 and m lt DegreeBound]
              cat [m : m in [2..DegreeBound-1] | not m in hints];
      bestK := 0;
      bestfit := 0;
      for m in degs do
        if Kbool then
          break;
        end if;
        vprintf Shimura : "trying degree %o\n", m;
        cfs_ind := 0;
        while not Kbool and cfs_ind lt #cfs do
          cfs_ind +:= 1;
          if Abs(cfs[cfs_ind]) lt eps then
            continue;
          end if;
          bl, K, v, conj, uCC := Propose(cfs[cfs_ind], m, Gate(m));
          if not bl then
            continue;
          end if;
          vprintf Shimura : "candidate K of degree %o from coefficient %o; verifying on all %o coefficients\n", m, cfs_ind, #cfs;
          ok, bad, rec := FitOverK(cfs, K, v, conj, true);
          if ok then
            Kbool := true;
          else
            vprintf Shimura : "rejected: coefficient %o does not fit\n", bad;
            rec := [];
            if bad - 1 gt bestfit then
              bestfit := bad - 1;
              bestK := K;
            end if;
          end if;
        end while;
      end for;
      if not Kbool and bestfit gt 0 then
        error Sprintf("Unable to create number field!  The best candidate, %o, fits the first %o coefficients of %o; raise prec (if it is the right field, the tail is too inaccurate; if a subfield, the primitive coefficients are)", bestK, bestfit, #cfs);
      end if;
    end if;
    if not Kbool then
      error "Unable to create number field!";
    end if;
    vprint Shimura : "... found!", K;
    vprint Shimura : "Recognizing coefficients...";
    Gamma`TriangleK := K;
    Gamma`TriangleKv := v;
    Gamma`TriangleKIsConjugated := conj;
    Gamma`TriangleKNumericalGenerator := uCC;
    if #rec ne #cfs then
      // the bound was right: fit ungated (the sanity check is the referee)
      ok, bad, rec := FitOverK(cfs, K, v, conj, false);
      error if not ok, Sprintf("Insufficient precision: coefficient %o of %o does not fit over %o; increase prec", bad, #cfs, K);
    end if;
    curve_coeffs := rec[1..#curve_coeffs];
    denom_coeffs := rec[#curve_coeffs+1..#curve_coeffs+#denom_coeffs];
    num_coeffs := rec[#curve_coeffs+#denom_coeffs+1..#cfs];
    Gamma`TriangleExactCurveCoefficients := curve_coeffs;
    ok, bad, urec := FitOverK([u], K, v, conj, false);
    error if not ok, Sprintf("Insufficient precision: the leading coefficient does not fit over %o; increase prec", K);
    u := urec[1];
    Gamma`TriangleExactBelyiMapLeadingCoefficient := u;
    Gamma`TriangleExactBelyiMapNumeratorCoefficients := num_coeffs;
    Gamma`TriangleExactBelyiMapDenominatorCoefficients := denom_coeffs;
    return Sprintf("Algebraic coefficients recognized and assigned for %o\n", Gamma);
  else
    error "Not implemented for nonhyperelliptic of arbitrary genus.";
  end if;
end intrinsic;

intrinsic TriangleMakeBelyiMap(Gamma::GrpPSL2Tri) -> Any
  {Given a GrpPSL2Tri with the number field K recognized and exact data computed construct the Belyi curve and Belyi map, then return and assign them.}
  sigma := Gamma`TriangleSigma;
  genus := Genus(Gamma);
  curve_coeffs := Gamma`TriangleExactCurveCoefficients;
  leading_coeff := Gamma`TriangleExactBelyiMapLeadingCoefficient;
  num_coeffs := Gamma`TriangleExactBelyiMapNumeratorCoefficients;
  denom_coeffs := Gamma`TriangleExactBelyiMapDenominatorCoefficients;
  K := Gamma`TriangleK;

  if genus eq 1 then
    // curve_invs := Gamma`TriangleExactCurveInvariants; // only for genus 1
    c4, c6 := Explode(curve_coeffs);
    X := EllipticCurve([-27*c4, -54*c6]);
    // assert [[jInvariant(E)] : E in curve_list] eq curve_invs_exact;
    Gamma`TriangleBelyiCurve := X;
    vprintf Shimura : "Assigned curve to Gamma\n";
    GenerateLSpaceBasis := function(n,KX);
      x := KX.1;
      y := KX.2;
      basis := [KX!1];
      for i in [2..n] do
        if i mod 2 eq 0 then
          Append(~basis,x^(i div 2));
        else //if i is odd
          Append(~basis, x^((i-3) div 2)*y);
        end if;
      end for;
      return basis;
    end function;
    lc := leading_coeff[1];
    KX<x,y> := FunctionField(X);
    Xbasis := GenerateLSpaceBasis(Maximum(#num_coeffs, #denom_coeffs),KX);
    phi_denom := KX!0;
    for i in [1..#denom_coeffs] do
      phi_denom := phi_denom + (KX!denom_coeffs[i])*Xbasis[i];
    end for;
    phi_num := KX!0;
    for i in [1..#num_coeffs] do
      phi_num := phi_num - (KX!num_coeffs[i])*Xbasis[i];
    end for;
    phi := (KX!lc)*phi_num/phi_denom;
    sane := BelyiMapSanityCheck(Gamma`TriangleSigma, X, phi);
    Gamma`TriangleBelyiMap := phi; // before error for debugging
    if not sane then
      print X, phi;
      error "FAILED SANITY CHECK!";
    end if;
  elif ((genus eq 2) or (assigned Gamma`TriangleIsHyperelliptic and Gamma`TriangleIsHyperelliptic)) then
    g := genus;
    // lc := leading_coeff[1];
    lc := leading_coeff; // this should be a number
    printf "lc = %o\n", lc;
    d := Gamma`TriangleD;
    Kt<t> := PolynomialRing(K);
    u := Kt!0;
    v := Kt!0;
    for i in [0..2*g+2] do
      v -:= curve_coeffs[i+1]*t^i;
    end for;
    for i in [0..g+1] do
      u -:= curve_coeffs[2*g+4+i]*t^i;
    end for;
    X := HyperellipticCurve(v,u);
    Gamma`TriangleBelyiCurve := X;
    // make Belyi map
    KX<x,y> := FunctionField(X);
    //s0 := #CycleDecomposition(sigma[1])[1];
    //t0 := d+g-s0; //Riemann-Roch
    s0, t0 := Explode(Gamma`TriangleRiemannRochParameters);
    num_basis := RiemannRochBasisHyperellipticExact(t0,X);
    denom_basis := RiemannRochBasisHyperellipticExact(s0+t0,X);

    phiX_denom := KX!0;
    for i in [1..#denom_coeffs] do
      phiX_denom := phiX_denom + (KX!denom_coeffs[i])*denom_basis[i];
    end for;
    phiX_num := KX!0;
    for i in [1..#num_coeffs] do
      phiX_num := phiX_num - (KX!num_coeffs[i])*num_basis[i];
    end for;
    phi := (KX!lc)*phiX_num/phiX_denom;
    sane := BelyiMapSanityCheck(Gamma`TriangleSigma, X, phi);
    Gamma`TriangleBelyiMap := phi; // before error for debugging
    if not sane then
      print X, phi;
      error "FAILED SANITY CHECK!";
    end if;
  elif (assigned Gamma`TriangleIsGenus3NonHyperelliptic and Gamma`TriangleIsGenus3NonHyperelliptic) then
    // Genus 3, not hyperelliptic: the canonical model is a smooth plane
    // quartic in P^2 with coordinates the echelonized basis f_1, f_2, f_3 of
    // S_2(Gamma), and the affine coordinates on the patch f_3 <> 0 are
    // x = f_1/f_3, y = f_2/f_3.  Everything is indexed by
    // Genus3NonHyperellipticMonomials (genus3nonhyperelliptic.m), which is
    // where that ordering is defined and where the numerical coefficients
    // were produced.
    lc := leading_coeff;   // a number, as in the hyperelliptic branch above
    dq := Gamma`TriangleGenus3NonHyperellipticDegree;
    qmons := Genus3NonHyperellipticMonomials(4);
    error if #curve_coeffs ne #qmons,
        Sprintf("expected %o quartic coefficients, got %o", #qmons, #curve_coeffs);
    // names deliberately unlike x, y, g, u, v, t: a polynomial ring with a
    // generator named g would silently rebind the genus, and Genus(X) eq g
    // would then compare against a ring generator while printing correctly
    PPq<uq0,uq1,uq2> := ProjectiveSpace(K, 2);
    // homogenize x^a*y^b as uq0^a*uq1^b*uq2^(4-a-b), so that uq0/uq2 = x and
    // uq1/uq2 = y: FunctionField's generators are the affine coordinates on
    // the patch where the LAST variable is 1
    Qq := &+[curve_coeffs[i]*uq0^(qmons[i][1])*uq1^(qmons[i][2])*uq2^(4-qmons[i][1]-qmons[i][2])
             : i in [1..#qmons]];
    X := Curve(PPq, Qq);
    error if not IsNonsingular(X),
        "the recovered plane quartic is singular; raise prec";
    gX := Genus(X);
    error if gX ne 3,
        Sprintf("the recovered plane quartic has genus %o, not 3; raise prec", gX);
    Gamma`TriangleBelyiCurve := X;
    vprintf Shimura : "Assigned plane quartic to Gamma\n";
    KXq<xq,yq> := FunctionField(X);
    qdmons := Genus3NonHyperellipticMonomials(dq);
    error if #num_coeffs ne #qdmons or #denom_coeffs ne #qdmons,
        Sprintf("expected %o numerator and denominator coefficients, got %o and %o",
                #qdmons, #num_coeffs, #denom_coeffs);
    // same sign convention as above: the numerator is accumulated with a
    // MINUS and lc multiplies the whole ratio, so that phi = lc*(-A)/B
    phiX_denom := KXq!0;
    for i in [1..#denom_coeffs] do
      phiX_denom := phiX_denom + (KXq!denom_coeffs[i])*xq^(qdmons[i][1])*yq^(qdmons[i][2]);
    end for;
    phiX_num := KXq!0;
    for i in [1..#num_coeffs] do
      phiX_num := phiX_num - (KXq!num_coeffs[i])*xq^(qdmons[i][1])*yq^(qdmons[i][2]);
    end for;
    phi := (KXq!lc)*phiX_num/phiX_denom;
    sane := BelyiMapSanityCheck(Gamma`TriangleSigma, X, phi);
    Gamma`TriangleBelyiMap := phi; // before error for debugging
    if not sane then
      print X, phi;
      error "FAILED SANITY CHECK!";
    end if;
  elif (assigned Gamma`TriangleIsGenus4Canonical and Gamma`TriangleIsGenus4Canonical) then
    // Genus 4, not hyperelliptic: the canonical model is a quadric meeting a
    // cubic in P^3 with coordinates the echelonized basis f_1, ..., f_4 of
    // S_2(Gamma), and the affine coordinates on the patch f_4 <> 0 are
    // x = f_1/f_4, y = f_2/f_4, z = f_3/f_4.  Everything is indexed by
    // Genus4Monomials (genus4.m), where the numerical coefficients were
    // produced: the curve list is Genus4Monomials(2) cat Genus4Monomials(3).
    lc := leading_coeff;
    dq := Gamma`TriangleGenus4FormDegree;
    mons2 := Genus4Monomials(2);
    mons3 := Genus4Monomials(3);
    error if #curve_coeffs ne #mons2 + #mons3,
        Sprintf("expected %o curve coefficients, got %o", #mons2 + #mons3, #curve_coeffs);
    // names deliberately unlike x, y, z, g, u, v, t: a ring generator named
    // g would silently rebind the genus
    PPq<uq0,uq1,uq2,uq3> := ProjectiveSpace(K, 3);
    // homogenize x^a y^b z^c as uq0^a uq1^b uq2^c uq3^(deg-a-b-c), so that
    // uq0/uq3 = x, uq1/uq3 = y, uq2/uq3 = z
    Hom := func<cfs, mons, deg | &+[cfs[i]*uq0^(mons[i][1])*uq1^(mons[i][2])*uq2^(mons[i][3])*uq3^(deg-mons[i][1]-mons[i][2]-mons[i][3])
                                     : i in [1..#mons]]>;
    Qq := Hom(curve_coeffs[1..#mons2], mons2, 2);
    Cq := Hom(curve_coeffs[#mons2+1..#mons2+#mons3], mons3, 3);
    X := Curve(PPq, [Qq, Cq]);
    error if not IsNonsingular(X),
        "the recovered quadric-and-cubic model is singular; raise prec";
    gX := Genus(X);
    error if gX ne 4,
        Sprintf("the recovered quadric-and-cubic model has genus %o, not 4; raise prec", gX);
    Gamma`TriangleBelyiCurve := X;
    vprintf Shimura : "Assigned quadric-and-cubic model to Gamma\n";
    KXq := FunctionField(X);
    qdmons := Genus4Monomials(dq);
    error if #num_coeffs ne #qdmons or #denom_coeffs ne #qdmons,
        Sprintf("expected %o numerator and denominator coefficients, got %o and %o",
                #qdmons, #num_coeffs, #denom_coeffs);
    // A and B as forms of the same degree; the ratio of two forms of equal
    // degree coerces into the function field of a curve in P^3, which is the
    // idiom that works there (M23-recompute/verify_modp.m).  Same sign
    // convention as above: phi = lc*(-A)/B.
    Aq := Hom(num_coeffs, qdmons, dq);
    Bq := Hom(denom_coeffs, qdmons, dq);
    phi := (KXq!lc)*(KXq!(-Aq/Bq));
    sane := BelyiMapSanityCheck(Gamma`TriangleSigma, X, phi);
    Gamma`TriangleBelyiMap := phi; // before error for debugging
    if not sane then
      print X, phi;
      error "FAILED SANITY CHECK!";
    end if;
  else
    error "Not implemented for nonhyperelliptic of arbitrary genus.";
  end if;
  vprint Shimura: "Belyi map successfully computed and verified!";
  return X, phi;
end intrinsic;

intrinsic TriangleMakeBelyiMaps(Gammas::SeqEnum[GrpPSL2Tri]) -> Any
  {Given a sequence of GrpPSL2Tri with the number field K recognized and exact data computed for each Gamma, construct the Belyi curves and Belyi maps.}
  for i := 1 to #Gammas do
    TriangleMakeBelyiMap(Gammas[i]);
  end for;
  return "\nAll Belyi maps computed, passed sanity, and assigned.";
end intrinsic;

/*
intrinsic GaloisSplitListsGenusZero(phisCC::List) -> Any
  {Given a list of lists of polynomials (or something) return a list of lists suitable as input for GaloisMinPoly.}
  // assert #phisCC[1] eq 3;
  // CC<I> := Parent(phisCC[1][1]);
  CC<I> := ComplexField(40);
  CCt<t> := PolynomialRing(CC);
  leading_coeffs := [phisCC[i][1] : i in {1..#phisCC}];
  num_coeffs := [phisCC[i][2] : i in {1..#phisCC}];
  denom_coeffs := [phisCC[i][3] : i in {1..#phisCC}];
  L := [];
  Append(~L, leading_coeffs);
  for i in {1..#num_coeffs[1]} do
    new := [];
    for j in {1..#phisCC} do
      Append(~new, num_coeffs[j][i]);
    end for;
    Append(~L, new);
  end for;
  for i in {1..#denom_coeffs[1]} do
    new := [];
    for j in {1..#phisCC} do
      Append(~new, denom_coeffs[j][i]);
    end for;
    Append(~L, new);
  end for;
  return L;
end intrinsic;
*/
