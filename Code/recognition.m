//For my advanced versions of rescaling (including automorphism group) of this, see genuszero lines 177 and 438

// TODO: Make sure TriangleRescaleCoefficients works for genus one.
// Once it does, delete previous rescaling functions
intrinsic TriangleRescaleCoefficients(Gamma::GrpPSL2, coeffs::SeqEnum, vals::SeqEnum : rescale_ind := 0) -> Any
  {Given a GrpPSL2 Gamma, and SeqEnums coeffs and vals, return the rescaling factor lamba, as well as the rescaled coefficients.  coeffs should be of the form [curve_coeffs, num_coeffs, denom_coeffs], and vals [curve_vals, num_vals, denom_vals]}
  g := Genus(Gamma);
  prec := Gamma`TriangleNumericalPrecision;
  eps := 10^(-prec/2);
  curve_coeffs, num_coeffs, denom_coeffs := Explode(coeffs);
  curve_vals, num_vals, denom_vals := Explode(vals);
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
  gcd, wts := Xgcd(nonzero_vals);
  // should gcd = aut? (no 09/19/17, well maybe)
  // assert gcd eq aut;
  print nonzero_inds;
  print gcd;
  print wts;
  wts_sum := &+[wts[i] : i in [1..#wts]];
  lambda := &*[all_coeffs[nonzero_inds[i]]^wts[i] : i in [1..#nonzero_inds]];
  if wts_sum ne 0 then
    if 0 in nonzero_vals then
      ind := Index(nonzero_vals,0);
      lambda := lambda*all_coeffs[nonzero_inds[ind]]^(-wts_sum);
      wts[ind] +:= -wts_sum; // FIXME maybe
    else
      error "Unable to create rescaling factor! No nonzero coefficients for weight zero :(";
    end if;
  end if;
  lambda := lambda^(1/gcd);
  // lambda := lambda^(1/aut);
  lambda := 1/lambda;

  // now rescale coefficients using lambda
  for i in [1..#curve_coeffs] do
    curve_coeffs[i] := curve_coeffs[i]*(lambda^curve_vals[i]);
  end for;
  curve_coeffs := [curve_coeffs[i]/curve_coeffs[#curve_coeffs] : i in [1..#curve_coeffs]];
  for i in [1..#num_coeffs] do
    num_coeffs[i] := num_coeffs[i]*(lambda^num_vals[i]);
  end for;
  for i in [1..#denom_coeffs] do
    denom_coeffs[i] := denom_coeffs[i]*(lambda^denom_vals[i]);
  end for;
  lc_num := num_coeffs[#num_coeffs];
  lc_den := denom_coeffs[#denom_coeffs];
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
intrinsic TriangleRecordCoefficients(Gammas::SeqEnum[GrpPSL2] : prec := 40) -> Any
  {Given a sequence of triangle subgroups (GrpPSL2s), write FldComElt invariants and coefficients for the curve and BelyiMap to the objects.}
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
    _:= TriangleUnitDisc(initial_Gamma : Precision := prec);
    Sk := TrianglePowerSeriesBasis(initial_Gamma, 2 : prec := prec);
    CC<I> := BaseRing(Parent(Sk[1][1]));
    DDs := initial_Gamma`TriangleDDs;
    // get numerical data for initial_Gamma
    _, rescale_ind, num_bool := TriangleGenusOneNumericalBelyiMap(Sk[1], initial_Gamma);
    if #Gammas ge 2 then
      for j in [2..#Gammas] do
        Gamma := Gammas[j];
        _:= TriangleUnitDisc(Gamma : Precision := prec);
        Sk := TrianglePowerSeriesBasis(Gamma, 2 : prec := prec);
        _, i_j, num_bool_j := TriangleGenusOneNumericalBelyiMap(Sk[1],Gamma : rescale_ind := rescale_ind, num_bool := num_bool);
        //need to make sure same indices of coefficients are used in computing lambda!
        if i_j ne rescale_ind or num_bool_j ne num_bool then
          error "Inconsistent rescaling index!\n";
        end if;
      end for;
    end if;
  elif genus eq 2 then
    _:= TriangleUnitDisc(initial_Gamma : Precision := prec);
    Sk := TrianglePowerSeriesBasis(initial_Gamma, 2 : prec := prec);
    CC<I> := BaseRing(Parent(Sk[1][1]));
    DDs := initial_Gamma`TriangleDDs;
    // get numerical data for initial_Gamma
    TriangleHyperellipticNumericalCoefficients(Sk, initial_Gamma);
    if #Gammas ge 2 then
      for j in [2..#Gammas] do
        Gamma := Gammas[j];
        _:= TriangleUnitDisc(Gamma : Precision := prec);
        Sk := TrianglePowerSeriesBasis(Gamma, 2 : prec := prec);
        TriangleHyperellipticNumericalCoefficients(Sk, Gamma);
      end for;
    end if;
  else
    error "Not implemented for genus greater than 2.";
  end if;
  return "Numerical data for given triangle subgroups computed and assigned.";
end intrinsic;

intrinsic TriangleRecordCoefficients(sigmas::SeqEnum[SeqEnum[GrpPermElt]] : prec := 40) -> Any
  {Given a sequence of permutation triples, write FldComElt invariants and coefficients for the curve and BelyiMap to the objects.}
  Gammas := [TriangleSubgroup(sigma) : sigma in sigmas];
  TriangleRecordCoefficients(Gammas : prec := prec);
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
          if #foobar gt 0 and not &and[IsSquare(foobarf) : foobarf in foobar] then
            error "Discriminant doesn't jive...try a higher precision";
          end if;
          if foobar eq [] then
            vprintf Shimura : "  ...number field found, with ps = %o and foobar = []\n", ps;
          else
            vprintf Shimura : "  ...number field found, with ps = %o and sqrt(foobar) = %o\n", ps, Round(Sqrt(CC!foobar[1]));
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

intrinsic TriangleLengthSort(Gammas::SeqEnum[GrpPSL2]) -> Any
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

intrinsic TriangleRecognizeCoefficients(Gammas::SeqEnum[GrpPSL2] : ExactAl := "GaloisOrbits", DegreeBound := 0) -> Any
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

intrinsic TriangleRecognizeAlgebraicCoefficients(Gamma::GrpPSL2 : DegreeBound := 0) -> Any
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
      Kbool, K, v, conj, uCC := MakeK(cfs[cfs_ind], DegreeBound : Gamma := Gamma);
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
  elif ((Genus(Gamma) eq 2) or (Gamma`TriangleIsHyperelliptic)) then
    vprint Shimura : "Looking for coefficient to recognize number field...";
    Kbool := false;
    curve_coeffs := Gamma`TriangleNumericalCurveCoefficients;
    u := Gamma`TriangleNumericalBelyiMapLeadingCoefficient;
    denom_coeffs := Gamma`TriangleNumericalBelyiMapDenominatorCoefficients;
    num_coeffs := Gamma`TriangleNumericalBelyiMapNumeratorCoefficients;
    cfs := curve_coeffs cat denom_coeffs cat num_coeffs;
    cfs_ind := 0;
    vprintf Shimura : "coefficients are %o\n", cfs;
    if DegreeBound eq 0 then
      sigma := Gamma`TriangleSigma;
      DegreeBound := #PassportRepresentatives(sigma : Pointed := true);
    end if;
    while not Kbool and cfs_ind lt #cfs do
      cfs_ind +:= 1;
      vprintf Shimura: "coefficients are %o\n", cfs_ind;
      Kbool, K, v, conj, uCC := MakeK(cfs[cfs_ind], DegreeBound : Gamma := Gamma);
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
    curve_coeffs := [RecognizeOverK(el,K,v,conj) : el in curve_coeffs];
    Gamma`TriangleExactCurveCoefficients := curve_coeffs;
    denom_coeffs := [RecognizeOverK(el,K,v,conj) : el in denom_coeffs];
    num_coeffs := [RecognizeOverK(el,K,v,conj) : el in num_coeffs];
    u := RecognizeOverK(u,K,v,conj);
    Gamma`TriangleExactBelyiMapLeadingCoefficient := u;
    Gamma`TriangleExactBelyiMapNumeratorCoefficients := num_coeffs;
    Gamma`TriangleExactBelyiMapDenominatorCoefficients := denom_coeffs;
    return Sprintf("Algebraic coefficients recognized and assigned for %o\n", Gamma);
  else
    error "Not implemented for nonhyperelliptic of arbitrary genus.";
  end if;
end intrinsic;

intrinsic TriangleMakeBelyiMap(Gamma::GrpPSL2) -> Any
  {Given a GrpPSL2 with the number field K recognized and exact data computed construct the Belyi curve and Belyi map, then return and assign them.}
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
  elif ((genus eq 2) or (Gamma`TriangleIsHyperelliptic)) then
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
  else
    error "Not implemented for nonhyperelliptic of arbitrary genus.";
  end if;
  vprint Shimura: "Belyi map successfully computed and verified!";
  return X, phi;
end intrinsic;

intrinsic TriangleMakeBelyiMaps(Gammas::SeqEnum[GrpPSL2]) -> Any
  {Given a sequence of GrpPSL2 with the number field K recognized and exact data computed for each Gamma, construct the Belyi curves and Belyi maps.}
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
