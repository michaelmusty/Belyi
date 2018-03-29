// update 23Jan2017 by MM to play nice with the database
// Note: For fundamental domains "close" to the boundary a higher prec is needed, but otherwise a lower prec (5 to 10) works best...

// TODO need this?
import "draw_data.m" : MachineZero;

/*
// TODO finish once database is stable
intrinsic TriangleDrawDessinToDatabase(Gamma::GrpPSL2 : prec := 8, Al := "Petal", filename := "", findSmallestCosets := false, pssetUnit := 7, includeLegend := true) -> MonStgElt
  {}
end intrinsic;
*/

intrinsic TriangleDrawDessinTexifyString(str::MonStgElt) -> MonStgElt
  {Replace all double backslashes with quadruple backslashes. Writing quadruple backslashes to file makes them double backslashes and then when reading database info into Magma double backslashes get you single backslashes...ya know...special characters!}
  nstr := "";
  l := Split(str, "\\" : IncludeEmpty := true);
  if str[1] eq "\\" then
    if str[#str] eq "\\" then // double backslashes at beginning and end
      for i in {2..#l} do
        nstr *:= Sprintf("\\\\%o", l[i]);
      end for;
      nstr *:= "\\\\";
    else // double backslash at beginning only
      for i in {2..#l} do
        nstr *:= Sprintf("\\\\%o", l[i]);
      end for;
    end if;
  else
    if str[#str] eq "\\" then // double backslash at end only
      for i in {1..#l} do
        nstr *:= Sprintf("%o\\\\", l[i]);
      end for;
    else // no double backslashes at beginning or end
      nstr *:= Sprintf("%o", l[1]);
      for i in {2..#l} do
        nstr *:= Sprintf("\\\\%o", l[i]);
      end for;
    end if;
  end if;
  return nstr;
end intrinsic;

intrinsic TriangleDrawDessinToFile(Gamma::GrpPSL2 : prec := 8, Al := "Petal", filename := "", findSmallestCosets := false, pssetUnit := 7, includeLegend := true) -> MonStgElt
  {Generates latex code to conformally draw a dessin for Gamma to a file in the current working directory. If filename is not specified, then a name is generated using the database naming convention.}
  str := TriangleDrawDessin(Gamma : prec := prec, Al := Al, filename := filename, findSmallestCosets := findSmallestCosets, pssetUnit := pssetUnit, includeLegend := includeLegend);
  if filename eq "" then
    // TODO change function when database name changes permanently
    sigma := Gamma`TriangleSigma;
    name := BelyiDBGenerateName(sigma);
  filename := Sprintf("%o/%o.tex", GetCurrentDirectory(), name);
    // filename := "/home/jvoight/Dropbox/toby/belyi/Examples/" cat name cat ".tex";
  else
    filename := filename;
  end if;
  SetOutputFile(filename : Overwrite := true);
  Write(filename, str : Overwrite := true);
  UnsetOutputFile();
  returnText := Sprintf("Latex file saved to %o",filename);
  return returnText;
end intrinsic;


intrinsic TriangleDrawDessin(Gamma::GrpPSL2 : prec := 8, Al := "Petal", filename := "", findSmallestCosets := false, pssetUnit := 7, includeLegend := true) -> MonStgElt
  {Returns a string of latex text to draw a conformal dessin for Gamma and saves the string to the Gamma attribute Gamma`TriangleDessin. The default precision is set to 8, but higher values may be needed for fundamental domains "close" to the boundary.}
  require IsTriangleSubgroup(Gamma) : "Gamma must be a triangle subgroup";
  /*
  drawing functions
  */
  MachineZero := function(y);
    prec := Precision(y);
    F := Parent(y);
    if (Abs(y) le 10^(-prec+2)) then
      // if IsWeaklyZero(y) then
      y := F!0.0;
    end if;
    return y;
  end function;
  HypLine := function(w1,w2,prec);
    RR := RealField(prec);
    CC := ComplexField(prec);
    w1x := MachineZero(RR!(Real(w1)));
    w1y := MachineZero(RR!(Imaginary(w1)));
    w2x := MachineZero(RR!(Real(w2)));
    w2y := MachineZero(RR!(Imaginary(w2)));
    A := Matrix(RR,2,2,[2*w1x,2*w2x,2*w1y,2*w2y]);
    x := Vector(RR,2,[w1x^2+w1y^2+1,w2x^2+w2y^2+1]);
    if MachineZero(AbsoluteValue(Determinant(A))) eq 0.0 then
      return <true,w1x,w1y,w2x,w2y>;
    else
      x0 := MachineZero(Solution(A,x)[1]);
      y0 := MachineZero(Solution(A,x)[2]);
      r := Sqrt((x0-w1x)^2+(y0-w1y)^2);
      anglew1 := (Arctan2(w1x-x0,w1y-y0))*(180/Pi(RR));
      anglew2 := (Arctan2(w2x-x0,w2y-y0))*(180/Pi(RR));
      if anglew1 le 0 then
        anglew1 := anglew1+360;
      end if;
      if anglew2 le 0 then
        anglew2 := anglew2+360;
      end if;
      HypLine1 := false;
      HypLine3 := x0;
      HypLine4 := y0;
      HypLine5 := r;
      HypLine6 := anglew1;
      HypLine7 := anglew2;
      if AbsoluteValue(anglew1-anglew2) le 180 then
        if anglew1 le anglew2 then
          HypLine2 := true;
        else
          HypLine2 := false;
        end if;
      else
        if anglew1 le anglew2 then
          HypLine2 := false;
        else
          HypLine2 := true;
        end if;
      end if;
      return <HypLine1,HypLine2,HypLine3,HypLine4,HypLine5,HypLine6,HypLine7>;
    end if;
  end function;
  Mid := function(w1,w2,prec);
    RR := RealField(prec);
    CC := ComplexField(prec);
    w1x := MachineZero(RR!(Real(w1)));
    w1y := MachineZero(RR!(Imaginary(w1)));
    w2x := MachineZero(RR!(Real(w2)));
    w2y := MachineZero(RR!(Imaginary(w2)));
    A := Matrix(RR,2,2,[2*w1x,2*w2x,2*w1y,2*w2y]);
    x := Vector(RR,2,[w1x^2+w1y^2+1,w2x^2+w2y^2+1]);
    midx := CC!1;
    midy := CC!1;
    if MachineZero(Determinant(A)) eq 0.0 then
      midx := (w1x+w2x)/2;
      midy := (w1y+w2y)/2;
    else
      x0 := MachineZero(Solution(A,x)[1]);
      y0 := MachineZero(Solution(A,x)[2]);
      r := Sqrt((x0-w1x)^2+(y0-w1y)^2);
      anglew1 := (Arctan2(w1x-x0,w1y-y0))*(180/Pi(RR));
      anglew2 := (Arctan2(w2x-x0,w2y-y0))*(180/Pi(RR));
      if anglew1 le 0 then
        anglew1 := anglew1+360;
      end if;
      if anglew2 le 0 then
        anglew2 := anglew2+360;
      end if;
      if AbsoluteValue(anglew1-anglew2) le 180 then
        if anglew1 le anglew2 then
          midx := x0+r*Cos(((anglew2-anglew1)/2+anglew1)*(Pi(RR)/180));
          midy := y0+r*Sin(((anglew2-anglew1)/2+anglew1)*(Pi(RR)/180));
        else
          midx := x0+r*Cos(((anglew1-anglew2)/2+anglew2)*(Pi(RR)/180));
          midy := y0+r*Sin(((anglew1-anglew2)/2+anglew2)*(Pi(RR)/180));
        end if;
      else
        if anglew1 le anglew2 then
          midx := x0+r*Cos(((anglew1+AbsoluteValue(anglew2-360))/2+(anglew2-360))*(Pi(RR)/180));
          midy := y0+r*Sin(((anglew1+AbsoluteValue(anglew2-360))/2+(anglew2-360))*(Pi(RR)/180));
        else
          midx := x0+r*Cos(((anglew2+AbsoluteValue(anglew1-360))/2+(anglew1-360))*(Pi(RR)/180));
          midy := y0+r*Sin(((anglew2+AbsoluteValue(anglew1-360))/2+(anglew1-360))*(Pi(RR)/180));
        end if;
      end if;
    end if;
    mid := CC!(midx+midy*Sqrt(-1));
    return mid;
  end function;
  DrawHypLine := function(w1,w2,prec : isDessinLine := false, scale := 1);
    line := HypLine(w1,w2,prec);
    if scale ne 1 then
      linewidth := RealField(prec)!(1.5*scale);
    else
      linewidth := RealField(prec)!(1.5);
    end if;
    if isDessinLine then
      if line[1] eq true then
        str := Sprintf("\\psline[linewidth=%opt]\n(%o,%o)\n(%o,%o)",linewidth,line[2],line[3],line[4],line[5]);
      else
        if line[2] eq true then
          str := Sprintf("\\psarc[linewidth=%opt]\n(%o,%o)\n{%o}\n{%o}\n{%o}",linewidth,line[3],line[4],line[5],line[6],line[7]);
        else
          str := Sprintf("\\psarcn[linewidth=%opt]\n(%o,%o)\n{%o}\n{%o}\n{%o}",linewidth,line[3],line[4],line[5],line[6],line[7]);
        end if;
      end if;
    else
      if line[1] eq true then
        str := Sprintf("\\psline[linewidth=.1pt]\n(%o,%o)\n(%o,%o)",line[2],line[3],line[4],line[5]);
      else
        if line[2] eq true then
          str := Sprintf("\\psarc[linewidth=.1pt]\n(%o,%o)\n{%o}\n{%o}\n{%o}",line[3],line[4],line[5],line[6],line[7]);
        else
          str := Sprintf("\\psarcn[linewidth=.1pt]\n(%o,%o)\n{%o}\n{%o}\n{%o}",line[3],line[4],line[5],line[6],line[7]);
        end if;
      end if;
    end if;
    return str;
  end function;
  DrawHypLineLabel := function(w1,w2,label,prec : isCosetLabel := false, scale := 1, color := "");
    if isCosetLabel eq true then
      if scale ne 1 then
        str := Sprintf("\n\\rput(%o,%o)\n{\\scalebox{%o}\n{\\psshadowbox[linewidth=.0001,fillcolor=lightestgray]\n{$%o$}}}",Real(Mid(w1,w2,prec)),Imaginary(Mid(w1,w2,prec)),scale,label);
      else
        str := Sprintf("\n\\rput(%o,%o)\n{\\psshadowbox[linewidth=.0001,fillcolor=lightestgray]\n{$%o$}}",Real(Mid(w1,w2,prec)),Imaginary(Mid(w1,w2,prec)),label);
      end if;
    else
      if scale ne 1 then
        if color ne "" then
          str := Sprintf("\n\\rput(%o,%o)\n{\\scalebox{%o}\n{\\psframebox*[linewidth=.0001,fillcolor=%o]\n{$%o$}}}",Real(Mid(w1,w2,prec)),Imaginary(Mid(w1,w2,prec)),scale,color,label);
        else
          str := Sprintf("\n\\rput(%o,%o)\n{\\scalebox{%o}\n{\\psframebox*[linewidth=.0001,fillcolor=lightestgray]\n{$%o$}}}",Real(Mid(w1,w2,prec)),Imaginary(Mid(w1,w2,prec)),scale,label);
        end if;
      else
        if color ne "" then
          str := Sprintf("\n\\rput(%o,%o)\n{\\psframebox*[linewidth=.0001,fillcolor=%o]\n{$%o$}}",Real(Mid(w1,w2,prec)),Imaginary(Mid(w1,w2,prec)),color,label);;
        else
          str := Sprintf("\n\\rput(%o,%o)\n{\\psframebox*[linewidth=.0001,fillcolor=lightestgray]\n{$%o$}}",Real(Mid(w1,w2,prec)),Imaginary(Mid(w1,w2,prec)),label);
        end if;
      end if;
    end if;
    return str;
  end function;
  DrawTriangle := function(vertices,prec);
    wa,wc,wb,wcStar := Explode(vertices);
    str := "\n\\pscustom[linewidth=.1pt]{\n";
    str *:= DrawHypLine(wa,wb,prec);
    str *:= "\n";
    str *:= DrawHypLine(wb,wc,prec);
    str *:= "\n";
    str *:= DrawHypLine(wc,wa,prec);
    str *:= "\n";
    str *:= Sprintf("\\closepath}");
    str *:= "\n\\pscustom[linewidth=.1pt,fillstyle=solid,fillcolor=lightgray]{\n";
    str *:= DrawHypLine(wa,wb,prec);
    str *:= "\n";
    str *:= DrawHypLine(wb,wcStar,prec);
    str *:= "\n";
    str *:= DrawHypLine(wcStar,wa,prec);
    str *:= "\n";
    str *:= "\\closepath}";
    str *:= "\n";
    return str;
  end function;
  DrawDessinLine := function(vertices,scale,prec);
    RR := RealField(prec);
    dotsize := RR!(scale*7);
    wa,wc,wb,wcStar := Explode(vertices);
    str := DrawHypLine(wa,wb,prec : isDessinLine := true, scale := scale);
    str *:= "\n";
    str *:= Sprintf("\\psdots*[dotstyle=o,dotsize=%opt](%o,%o)\n",dotsize,MachineZero(RR!(Real(wa))),MachineZero(RR!(Imaginary(wa))));
    str *:= Sprintf("\\psdots*[dotstyle=*,dotsize=%opt](%o,%o)\n",dotsize,MachineZero(RR!(Real(wb))),MachineZero(RR!(Imaginary(wb))));
    str *:= Sprintf("\\psdots*[dotstyle=x,dotsize=%opt](%o,%o)\n",dotsize,MachineZero(RR!(Real(wc))),MachineZero(RR!(Imaginary(wc))));
    return str;
  end function;
  /*
  main
  */
  Delta := ContainingTriangleGroup(Gamma);
  sigma := DefiningPermutation(Gamma);
  sigma0, sigma1, sigmaoo := Explode(sigma);
  pi := DefiningPermutationRepresentation(Gamma);
  d := IndexDegree(Gamma);
  HH := UpperHalfPlane();
  DD := TriangleUnitDisc(Gamma);
  RR := RealField(prec);
  CC := ComplexField(prec);
  if Al eq "Full" then
    cosets, cosetGraph, sidepairing := TriangleCosetRepresentatives(Gamma : Al := "Full", FindSmallestCosets := findSmallestCosets);
  else
    cosets, cosetGraph, sidepairing := TriangleCosetRepresentatives(Gamma : FindSmallestCosets := findSmallestCosets);
  end if;
  sidePairing := [];
  usedSides := [];
  for i in {1..#sidepairing} do
    if ((sidepairing[i][2] notin usedSides) and (sidepairing[i][3] notin usedSides)) then
      Append(~sidePairing,sidepairing[i]);
      Append(~usedSides,sidepairing[i][2]);
      Append(~usedSides,sidepairing[i][3]);
    end if;
  end for;
  // print #sidePairing;
  GammaFD := FundamentalDomain(Gamma, DD);
  scales := [];
  for i in {1..#cosets} do
    distances := [];
    for j,k in {4*(i-1)+1,4*(i-1)+2,4*(i-1)+3,4*(i-1)+4} do
      if MachineZero(RR!(Abs(ComplexValue(GammaFD[j])-ComplexValue(GammaFD[k])))) ne 0 then
        Append(~distances,RR!(Abs(ComplexValue(GammaFD[j])-ComplexValue(GammaFD[k]))));
        // print j,k, RR!(Abs(ComplexValue(GammaFD[j])-ComplexValue(GammaFD[k])));
      end if;
    end for;
    Append(~scales,Min(distances));
  end for;
  for i in {1..#scales} do
    scales[i] := Min(scales[i]*6,1);
    if scales[i] le RR!(0.03) then
      scales[i] := RR!(0.03);
    end if;
  end for;
  // print scales;
  str := Sprintf("\\documentclass{article}\n\\usepackage{pstricks}\n\\usepackage{auto-pst-pdf}\n\\usepackage{booktabs}\n\\begin{document}\n\\begin{center}\n\\psset{unit=%ocm}\n\\begin{pspicture}(-1,-1)(1,1)\n\\pscircle[linewidth=.001pt](0,0){1}\n\\newgray{lightestgray}{.93}\n",pssetUnit);
  str *:= "\n% draw the triangles\n";
  for i in {1..#cosets} do
    wa := GammaFD[4*(i-1)+1];
    wc := GammaFD[4*(i-1)+2];
    wb := GammaFD[4*(i-1)+3];
    wcStar := GammaFD[4*(i-1)+4];
    vertices := [wa,wc,wb,wcStar];
    str *:= "\n";
    str *:= DrawTriangle(vertices,prec);
  end for;
  str *:= "\n\n% label the sides\n\n";
  for i in {1..#sidePairing} do
    firstCosetNumber := sidePairing[i][2][1];
    if sidePairing[i][2][2] eq Delta.1^(-1) then
      w1 := GammaFD[4*(firstCosetNumber-1)+1];
      w2 := GammaFD[4*(firstCosetNumber-1)+2];
    elif sidePairing[i][2][2] eq Delta.2 then
      w1 := GammaFD[4*(firstCosetNumber-1)+2];
      w2 := GammaFD[4*(firstCosetNumber-1)+3];
    elif sidePairing[i][2][2] eq Delta.2^(-1) then
      w1 := GammaFD[4*(firstCosetNumber-1)+3];
      w2 := GammaFD[4*(firstCosetNumber-1)+4];
    else
      w1 := GammaFD[4*(firstCosetNumber-1)+4];
      w2 := GammaFD[4*(firstCosetNumber-1)+1];
    end if;
    secondCosetNumber := sidePairing[i][3][1];
    if sidePairing[i][3][2] eq Delta.1^(-1) then
      w3 := GammaFD[4*(secondCosetNumber-1)+1];
      w4 := GammaFD[4*(secondCosetNumber-1)+2];
    elif sidePairing[i][3][2] eq Delta.2 then
      w3 := GammaFD[4*(secondCosetNumber-1)+2];
      w4 := GammaFD[4*(secondCosetNumber-1)+3];
    elif sidePairing[i][3][2] eq Delta.2^(-1) then
      w3 := GammaFD[4*(secondCosetNumber-1)+3];
      w4 := GammaFD[4*(secondCosetNumber-1)+4];
    else
      w3 := GammaFD[4*(secondCosetNumber-1)+4];
      w4 := GammaFD[4*(secondCosetNumber-1)+1];
    end if;
    // str *:= DrawSidePairingArrow(w1,w2,prec,true);
    // str *:= DrawSidePairingArrow(w3,w4,prec,false);
    str *:= DrawHypLineLabel(w1,w2,Sprintf("s_{%o}",i),prec : scale := scales[firstCosetNumber],color := "blue!10");
    str *:= DrawHypLineLabel(w3,w4,Sprintf("s_{%o}",i),prec : scale := scales[secondCosetNumber],color := "red!80");
  end for;
  str *:= "\n\n% draw the dessin\n";
  for i in {1..#cosets} do
    wa := GammaFD[4*(i-1)+1];
    wc := GammaFD[4*(i-1)+2];
    wb := GammaFD[4*(i-1)+3];
    wcStar := GammaFD[4*(i-1)+4];
    vertices := [wa,wc,wb,wcStar];
    str *:= "\n";
    str *:= "%";
    str *:= Sprintf(" coset %o\n",i);
    str *:= DrawDessinLine(vertices,scales[i],prec);
    str *:= "\n";
  end for;
  str *:= "\n% label the cosets\n\n";
  for i in {1..#cosets} do
    w1 := GammaFD[4*(i-1)+1];
    w2 := GammaFD[4*(i-1)+3];
    str *:= DrawHypLineLabel(w1,w2,IntegerToString(i),prec : isCosetLabel := true, scale := scales[i]);
  end for;
  str *:= "\n\n\\end{pspicture}\n\\end{center}\n";
  if includeLegend then
    str *:= "\n\n% include legend\n\n";
    str *:= "\\begin{center}\n\\begin{tabular}{ll}\n\\toprule\nLabel & Coset Representative\\\\\n\\midrule\n";
    alphas := [];
    for i in {1..#cosets} do
      Append(~alphas,Eltseq(cosets[i]));
    end for;
    for i in {1..#cosets} do
      if i eq 1 then
        str *:= Sprintf("$%o$ & %o \\\\\n",i,"1");
      else
        j := 1;
        temp := "";
        repeat
          if Abs(alphas[i][j]) eq 1 then
            exponent := Sign(alphas[i][j]);
            count := 1;
            if j+1 le #alphas[i] then
              k := j+1;
              while (Abs(alphas[i][k]) eq 1) and (k le #alphas[i]) do
                exponent := exponent+Sign(alphas[i][k]);
                k +:= 1;
                count +:= 1;
                if k gt #alphas[i] then
                  break;
                end if;
              end while;
            end if;
            if exponent eq 1 then
              exponent := "";
            end if;
            temp *:= Sprintf("\\delta_a^{%o}",exponent);
            j +:= count;
          else
            exponent := Sign(alphas[i][j]);
            count := 1;
            if j+1 le #alphas[i] then
              k := j+1;
              while (Abs(alphas[i][k]) eq 2) and (k le #alphas[i]) do
                exponent := exponent+Sign(alphas[i][k]);
                k +:= 1;
                count +:= 1;
                if k gt #alphas[i] then
                  break;
                end if;
              end while;
            end if;
            if exponent eq 1 then
              exponent := "";
            end if;
            temp *:= Sprintf("\\delta_b^{%o}",exponent);
            j +:= count;
          end if;
        until j gt #alphas[i];
        str *:= Sprintf("$%o$ & $%o$ \\\\\n",i,temp);
      end if;
    end for;
    str *:= "\\bottomrule\n\\end{tabular}\n";
    str *:= "\\hfill\n";
    str *:= "\\begin{tabular}{ll}\n\\toprule\nLabel & Side Pairing Element\\\\\n\\midrule\n";
    alphas := [];
    for i in {1..#sidePairing} do
      Append(~alphas,Eltseq(sidePairing[i][1]));
    end for;
    for i in {1..#sidePairing} do
      j := 1;
      temp := "";
      repeat
        if Abs(alphas[i][j]) eq 1 then
          exponent := Sign(alphas[i][j]);
          count := 1;
          if j+1 le #alphas[i] then
            k := j+1;
            while (Abs(alphas[i][k]) eq 1) and (k le #alphas[i]) do
              exponent := exponent+Sign(alphas[i][k]);
              k +:= 1;
              count +:= 1;
              if k gt #alphas[i] then
                break;
              end if;
            end while;
          end if;
          if exponent eq 1 then
            exponent := "";
          end if;
          temp *:= Sprintf("\\delta_a^{%o}",exponent);
          j +:= count;
        else
          exponent := Sign(alphas[i][j]);
          count := 1;
          if j+1 le #alphas[i] then
            k := j+1;
            while (Abs(alphas[i][k]) eq 2) and (k le #alphas[i]) do
              exponent := exponent+Sign(alphas[i][k]);
              k +:= 1;
              count +:= 1;
              if k gt #alphas[i] then
                break;
              end if;
            end while;
          end if;
          if exponent eq 1 then
            exponent := "";
          end if;
          temp *:= Sprintf("\\delta_b^{%o}",exponent);
          j +:= count;
        end if;
      until j gt #alphas[i];
      str *:= Sprintf("$s_{%o}$ & $%o$ \\\\\n",i,temp);
    end for;
    str *:= "\\bottomrule\n\\end{tabular}\n";
    str *:= "\\end{center}\n";
  end if;
  str *:= "\n\\thispagestyle{empty}\n\\end{document}\n";
  Gamma`TriangleDessin := str;
  return str;
end intrinsic;
