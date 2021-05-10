intrinsic SphericalBelyiMap(sigma::SeqEnum[GrpPermElt]) -> FldFunFracSchElt
  {Spherical triples and Belyi maps, hard-coded.  JV}
  PP1 := Curve(ProjectiveSpace(PolynomialRing(Rationals(), 2)));
  KPP1<x> := FunctionField(PP1);

  sigmacyc := {CycleStructure(sigma_s) : sigma_s in sigma};

  abc := [Order(sigma_s) : sigma_s in sigma];
  abc_sorted := Sort(abc);
  d := Degree(Parent(sigma[1]));

  if abc_sorted[1] eq 1 then
    assert abc_sorted[2] eq abc_sorted[3];
    phix := x^abc_sorted[3];
    if abc[1] eq 1 then
      phix := phix-1; // 1-phix?
    else
      phix := 1/(1-phix);
    end if;
  elif abc_sorted[1..2] eq [2,2] then
    if abc_sorted[3] eq 2 then
      phix := -(x*(x-1)/(x-1/2))^2;
    else
      cheb_bool := false;
      sigmacyc_seq := SetToSequence(sigmacyc);
      for s in [1..#sigmacyc_seq] do
        cycs := sigmacyc_seq[s];
        for i := 1 to #cycs do
          if cycs[i][1] eq 1 then
            cheb_bool := true;
            one_one_cycle := s;
          end if;
          if cycs[i][1] eq d then
            d_cycle := s;
          end if;
        end for;
      end for;
      if cheb_bool then
        vprint Shimura : "Chebyshev spherical Belyi map";
        assert assigned one_one_cycle;
        assert one_one_cycle ne d_cycle;
        phix := (Evaluate(ChebyshevFirst(abc_sorted[3]),x)+1)/2;
        if one_one_cycle eq 2 then
          if d_cycle eq 1 then
            phix := 1/phix;
          end if;
        elif one_one_cycle eq 1 then
          if d_cycle eq 2 then
            phix := 1 - 1/phix;
          elif d_cycle eq 3 then
            phix := 1 - phix;
          end if;
        else
          assert one_one_cycle eq 3;
          if d_cycle eq 1 then
            phix := 1/(1-phix);
          elif d_cycle eq 2 then
            phix := 1 - 1/(1 - phix);
          end if;
        end if;
        /*
        if abc[1] ne 2 then
          phix := 1/phix;
        elif abc[2] ne 2 then
          phix := 1-1/(1-phix); // should this be 1-1/(1-phix) as below?
        end if;
        */
      else
        vprint Shimura : "Dihedral spherical Belyi map";
        phix := (-1/4)*(x^abc_sorted[3] + 1/x^abc_sorted[3]) + 1/2; // this is the answer for [2,2,3]
        // TODO: S3 action doesn't currently work.  FIXME!
        if abc[1] ne 2 then
          vprint Shimura : "abc = [m,2,2]; swapping 0 and oo";
          phix := 1/phix;
        elif abc[2] ne 2 then
          vprint Shimura : "abc = [2,m,2]; swapping 1 and oo";
          phix := 1 - 1/(1-phix);
        end if;
      end if;
    end if;
  elif abc_sorted eq [2,3,3] then
    // tetrahedral case = A_4
    // there are 3 faithful transitive permutation reps of A_4
    if d eq 4 then
      phix := (x^2 - 3/2*x - 3/16)^2/x;
    elif d eq 6 then
      phix := -2566296/357911*(x-15/2)*(x-19/12)*(x^2-357/109*x+3)^2/(x^2-3)^3;
    elif d eq 12 then
      phix := -(x^6-20*x^3-8)^2/2^6/(x^3-1)^3;
    end if;
    if abc[2] eq 2 then
      phix := phix-1;
    elif abc[3] eq 2 then
      phix := 1/phix;
    end if;
  elif abc_sorted eq [2,3,4] then
    // octahedral case = S_4
    if d eq 4 then
      phix := 243*(x-1/2)^2*(x^2-17/9*x+11/12);
    elif d eq 6 and sigmacyc eq {[<2,3>],[<3,2>],[<4,1>,<1,2>]} then
      phix := -16/27*x^2*(x^2-9/4)^2/(x^2-2);
    elif d eq 6 and sigmacyc eq {[<2,2>,<1,2>],[<3,2>],[<4,1>,<2,1>]} then
      phix := -1/108*(x^2-2)^2*(x^2+16)/x^2;
    elif d eq 8 then
      phix := 16/27*(x^2+1/8)^2*(x^2+2*x-1/8)^2/x^4;
    elif d eq 12 and sigmacyc eq {[<2,6>],[<3,4>],[<4,2>,<2,2>]} then
      phix := -1/108*(x^2+8)^2*(x^2-4)^2*(x^2+2)^2/x^4/(x^2+4)^2;
    elif d eq 12 and sigmacyc eq {[<2,5>,<1,2>],[<3,4>],[<4,3>]} then
      phix := -1/108*(x-2)^2*(x^2+4*x-4)*(x^4+2*x^2-4*x+2)^2/(x*(x-1))^4;
    elif d eq 24 then
      phix := -(x^12-33*x^8-33*x^4+1)^2/(2^2*3^3*(x*(x^4-1))^4);
    end if;
    if abc eq [2,4,3] then
      phix := phix/(1-phix);
    elif abc eq [3,2,4] then
      phix := 1-phix;
    elif abc eq [3,4,2] then
      phix := 1/phix-1;
    elif abc eq [4,2,3] then
      phix := 1/(1-phix);
    elif abc eq [4,3,2] then
      phix := 1/phix;
    end if;
  elif abc_sorted eq [2,3,5] then
    // icosahedral case = A_5
    if d eq 5 then
      phix := 9/2*x*(x^2-5/3*x+5/4)^2;
    elif d eq 6 then
      phix := 9/2*(x^2-11/3*x+125/36)*(x^2-2/3*x-1/36)^2/x;
    elif d eq 10 then
      /* Descends!
      F<gld> := NumberField(Polynomial([-1,1,1]));
      PP1 := Curve(ProjectiveSpace(PolynomialRing(F, 2)));
      KPP1<x> := FunctionField(PP1);
      phix := 1/1728*(-34100*gld-55175)*
              ((x + 1/5*(-3*gld + 1))*(x + 3*gld - 1)*
               (x^2 + 1/5*(-8*gld + 6)*x - 8*gld + 5))^2*
               (x^2 + 1/5*(22*gld - 14)*x - 55*gld + 34)/x^5;
      */
      phix := (x^2-2*x+21/20)*(x^2-2*x+9/5)^2*(x^2+1/2*x-19/20)^2 / (x^2-x-1/5)^5;
    elif d eq 12 then
      phix := -1/1728*(x^2+1)^2*(x^4-522*x^3-10006*x^2+522*x+1)^2/(x*(x^2-11*x-1)^5);
    elif d eq 15 then
      phix := -1/1728*(x+2)*(x^2-20)*((x^2+5)*(x^4+14*x^3+74*x^2+170*x+145))^2/(x^2+5*x+5)^5;
    elif d eq 20 then
      /* Descends!
      F<gld> := NumberField(Polynomial([-1,1,1]));
      PP1 := Curve(ProjectiveSpace(PolynomialRing(F, 2)));
      KPP1<x> := FunctionField(PP1);
      phix := (-275*gld + 175)/1728*
              ((x^2 + 1/5*(-gld + 1))*
               (x^2 + 1/5*(-14*gld - 22)*x + 1/5*(gld - 1))*
               (x^2 + 1/5*(4*gld + 2)*x + 1/5*(gld - 1))*
               (x^4 - 2*x^3 + 1/5*(6*gld + 11)*x^2 + 1/5*(-2*gld + 2)*x + 1/25*(-3*gld + 2)))^2/
              (x*(x + 1/5*(-2*gld - 1))*(x + 1/5*(3*gld - 1)))^5;
      */
      f := (-49/576)*((x^2 + 4/5)*(x^4 - 20*x^3 + 168/5*x^2 + 16*x + 16/25)*
                      (x^4 - 20/7*x^3 + 36/35*x^2 + 16/7*x + 16/25))^2/
                     (x^4 - 2*x^3 - 12/5*x^2 + 8/5*x + 16/25)^5;
      /* Pointed descent:
      f := (64009/9)*((x^2 + 1/3*x + 3/10)*(x^4 + 19/11*x^3 + 83/330*x^2 - 109/330*x + 191/9900)*
                      (x^4 + 62/23*x^3 + 677/345*x^2 - 12/115*x + 8/575))^2/
                     (x^4 - 4*x^3 - 106/15*x^2 - 11/15*x + 29/225)^5;
      */

    elif d eq 30 then
      phix := -1/1728*(x^2+4)*((x^2-2*x-4)*(x^4-4*x^3+21*x^2-34*x+41)*
                               (x^4+3*x^2+1)*(x^4+6*x^3+21*x^2+36*x+61))^2/
               ((x-1)*(x^4+x^3+6*x^2+6*x+11))^5;
    elif d eq 60 then
      phix := -(x^30-522*x^25-10005*x^20-10005*x^10+522*x^5+1)^2/(2^6*3^3*(x*(x^10-11*x^5-1))^5);
    end if;
    if abc eq [2,5,3] then
      phix := phix/(1-phix);
    elif abc eq [3,2,5] then
      phix := 1-phix;
    elif abc eq [3,5,2] then
      phix := 1/phix-1;
    elif abc eq [5,2,3] then
      phix := 1/(1-phix);
    elif abc eq [5,3,2] then
      phix := 1/phix;
    end if;
  end if;

  return PP1, phix;
end intrinsic;

intrinsic EuclideanBelyiMap(sigma::SeqEnum[GrpPermElt]) -> FldFunFracSchElt
  {Euclidean triples and Belyi maps, finitely many hard-coded, the rest computed using isogenies.  JV}
  abc := [Order(sigma_s) : sigma_s in sigma];
  abc_sorted := Sort(abc);
  d := Degree(Parent(sigma[1]));

  sigmacyc := {CycleStructure(sigma_s) : sigma_s in sigma};

	Sd := Universe(sigma);
	d := Degree(Sd);
	G := sub<Sd | sigma>;
	Gcom := CommutatorSubgroup(G);
	Gcom := AbelianGroup(Gcom);
	Gcom_inv := InvariantFactors(Gcom);
	assert #Gcom_inv le 2;

  if #Gcom_inv eq 0 then
    Gcom_inv := [1];
  end if;

  if #Gcom_inv eq 1 then
		isogDegree := Gcom_inv[1];
	else
	  assert Gcom_inv[2] mod Gcom_inv[1] eq 0;
		isogDegree := Gcom_inv[2] div Gcom_inv[1];
	end if;

  if abc_sorted in [[2,3,6],[3,3,3]] then
  	K<omega> := NumberField(Polynomial([1,1,1]));
    X0 := EllipticCurve([K | 0,1]);
  else
    K<i> := NumberField(Polynomial([1,0,1]));
    X0 := EllipticCurve([K | -1,0]);
  end if;

	if isogDegree gt 1 then
  	isogPol := Factorization(DivisionPolynomial(X0,isogDegree))[1][1];
  	X, psich := IsogenyFromKernel(X0,isogPol);
  	psi := DualIsogeny(psich);
  	if #Gcom_inv eq 2 then
	  	phip := psi*MultiplicationByMMap(X0,Gcom_inv[1]);
	  else
		  phip := psi;
	  end if;
	else
	  X := X0;
	  phip := MultiplicationByMMap(X0,Gcom_inv[1]);
	end if;

  if abc_sorted eq [2,3,6] then
    if d eq 6 and sigmacyc eq {[<2,3>],[<3,2>],[<6,1>]} then
      // G		6T1     2,3,6   size=1  g=1     2^3;3^2;6^1;(1, 4)(2, 5)(3, 6);(1, 3, 5)(2, 4, 6);(1, 2, 3, 4, 5, 6)
      X := EllipticCurve([0,-1]);
      KX<x,y> := FunctionField(X);
      phi := x^3;
    elif d eq 6 and sigmacyc eq {[<2,3>],[<3,1>,<1,3>],[<6,1>]} then
      // N		6T5     2,3,6   size=1  g=0     2^3;3^1,1^3;6^1;(1, 4)(2, 5)(3, 6);(1, 3, 5);(1, 4, 5, 2, 3, 6)
      X := Curve(ProjectiveSpace(PolynomialRing(Rationals(), 2)));
      KX<x> := FunctionField(X);
      phi := 4*(x^3+1/2)^2;
    elif d eq 6 and sigmacyc eq {[<2,1>,<1,4>],[<3,2>],[<6,1>]} then
      // N		6T6     2,3,6   size=1  g=0     2^1,1^4;3^2;6^1;(1, 4);(1, 3, 5)(2, 4, 6);(1, 2, 6, 4, 5, 3)
      X := Curve(ProjectiveSpace(PolynomialRing(Rationals(), 2)));
      KX<x> := FunctionField(X);
      phi := 9*x^2*(3*x^4-3*x^2+1);
    else
	    if #G/d eq 6 then
				extractx3 := function(g);
					// if g = f(x^3), return f
					cf := Coefficients(g);
					assert &and[cf[i] eq 0 : i in [1..#cf] | i mod 3 ne 1];
					return Polynomial([cf[i] : i in [1..#cf] | i mod 3 eq 1]);
				end function;

      	_<x> := FunctionField(K);
				phi3 := Evaluate(DefiningEquations(phip)[1]/DefiningEquations(phip)[3],[x,0,1])^3;
				phi := extractx3(Numerator(phi3))/extractx3(Denominator(phi3));

				X := Curve(ProjectiveSpace(PolynomialRing(K, 2)));
				KX<x> := FunctionField(X);
				phi := -Evaluate(phi,x);
			elif #G/d eq 3 then
        extracty := function(g,X);
					// if g = f(x^3,y), return f(y^2+c,y)
					assert Coefficients(X)[1..4] eq [0,0,0,0];  // make it y^2 = x^3 + c
					c := Coefficients(X)[5];
					_<y> := FunctionField(K);
					mons := Monomials(g);
					cfs := Coefficients(g);
					v := 0;
					for i := 1 to #mons do
						dx := Degree(mons[i],1);
						assert dx mod 3 eq 0;
						v +:= cfs[i]*(y^2-c)^(dx div 3)*y^Degree(mons[i],2);
					end for;
					return v;
				end function;

        KX<x,y> := FunctionField(X);
				phi3 := Evaluate(DefiningEquations(phip)[1]/DefiningEquations(phip)[3],[x,y,1])^3;
				phi := extracty(Numerator(phi3),X)/extracty(Denominator(phi3),X);

				X := Curve(ProjectiveSpace(PolynomialRing(K, 2)));
				KX<x> := FunctionField(X);
				phi := -Evaluate(phi,x);
			elif #G/d eq 1 then
        KX<x,y> := FunctionField(X);
        phi := Evaluate(DefiningEquations(phip)[1]/DefiningEquations(phip)[3],[x,y,1])^3;
			else
				error "Only implemented full or trivial quotients so far; please complain! :)";
    	end if;
    end if;
  elif abc_sorted eq [3,3,3] then
    if d eq 4 then
      // genus 0
      X := Curve(ProjectiveSpace(PolynomialRing(Rationals(), 2)));
      KX<x> := FunctionField(X);
      phi := -4*x^3*(x-1)/(x-1/4);
    elif d eq 6 then
      // N		6T4     3,3,3   size=1  g=1     3^2;3^2;3^2;(1, 3, 5)(2, 4, 6);(1, 3, 2)(4, 6, 5);(1, 6, 5)(2, 4, 3)
      X := EllipticCurve([-15,22]);
      KX<x,y> := FunctionField(X);
      phi := (-1/16*x^2 + 1/4*x - 7/16)/(x^2 - 4*x + 4)*y + 1/2;
    else
      if #G/d eq 3 then
        extracty := function(g,X);
					// if g = f(x^3,y), return f(y^2+c,y)
					assert Coefficients(X)[1..4] eq [0,0,0,0];  // make it y^2 = x^3 + c
					c := Coefficients(X)[5];
					_<y> := FunctionField(K);
					mons := Monomials(g);
					cfs := Coefficients(g);
					v := 0;
					for i := 1 to #mons do
						dx := Degree(mons[i],1);
						assert dx mod 3 eq 0;
						v +:= cfs[i]*(y^2-c)^(dx div 3)*y^Degree(mons[i],2);
					end for;
					return v;
				end function;

        KX<x,y> := FunctionField(X);
				phi2 := Evaluate(DefiningEquations(phip)[2]/DefiningEquations(phip)[3],[x,y,1]);
				phi := extracty(Numerator(phi2),X)/extracty(Denominator(phi2),X);

				X := Curve(ProjectiveSpace(PolynomialRing(K, 2)));
				KX<x> := FunctionField(X);
				phi := (1-Evaluate(phi,x))/2;
			elif #G/d eq 1 then
        KX<x,y> := FunctionField(X);
        phi := Evaluate(DefiningEquations(phip)[2]/DefiningEquations(phip)[3],[x,y,1]);
        phi := (1-phi)/2;
			else
				error "Only implemented full or trivial quotients so far; please complain! :)";
      end if;
    end if;
  elif abc_sorted eq [2,4,4] then
    if d eq 4 then
      X := EllipticCurve([-1,0]);
      KX<x,y> := FunctionField(X);
      phi := x^2;
    elif d eq 5 then
      // genus 0
      K<i> := NumberField(Polynomial([1,0,1]));
      X := Curve(ProjectiveSpace(PolynomialRing(K, 2)));
      KX<x> := FunctionField(X);
      phi := (-136*i+4623)/4107*x^4*(x+111)/((x-74*i+37)*(x^2+(57*i+9)*x+4662*i-8991)^2);
    elif d eq 6 then
      // N		6T10    2,4,4   size=2  g=0     2^2,1^2;4^1,2^1;4^1,2^1;(1, 5)(2, 4);(1, 2, 5, 6)(3, 4);(1, 2, 3, 4)(5, 6)
      K<nu> := NumberField(Polynomial([-3,0,1]));
      X := Curve(ProjectiveSpace(PolynomialRing(K, 2)));
      KX<x> := FunctionField(X);
      phi := (x^6 - 2*x^5 + x^4 + 1/9*(2*nu + 3)*x^2 + 1/27*(-8*nu - 14)*x + 1/243*(26*nu + 45))/(x^6 - 2*x^5 + x^4);
    else
      if #G/d eq 4 then
        extractx2 := function(g);
          // if g = f(x^3), return f
          cf := Coefficients(g);
          assert &and[cf[i] eq 0 : i in [1..#cf] | i mod 2 ne 1];
          return Polynomial([cf[i] : i in [1..#cf] | i mod 2 eq 1]);
        end function;
        _<x> := FunctionField(K);
        phi2 := Evaluate(DefiningEquations(phip)[1]/DefiningEquations(phip)[3],[x,0,1])^2;
        phi := extractx2(Numerator(phi2))/extractx2(Denominator(phi2));
        X := Curve(ProjectiveSpace(PolynomialRing(K, 2)));
        KX<x> := FunctionField(X);
        phi := 1-Evaluate(phi,x);
      elif #G/d eq 1 then
        KX<x,y> := FunctionField(X);
        phi := Evaluate(DefiningEquations(phip)[1]/DefiningEquations(phip)[3],[x,y,1])^2;
      else
        error "Only implemented full or trivial quotients so far; please complain! :)";
      end if;
    end if;
    if abc[2] eq 2 then
      phi := 1-phi;
    elif abc[3] eq 2 then
      phi := 1/phi;
    end if;
  end if;
  return X, phi;
end intrinsic;
