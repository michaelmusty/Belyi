// petri_stage0.m -- Stage 0 of Doc/SPEC-genus5plus.md §8: the Petri
// class of the degree-11 genus-5 passports, from the power series alone.
// No recognition, no maps.
//
//   magma -b Code/petri_stage0.m < /dev/null                 # 11T5, both members, prec 30
//   magma -b which:=11T6 Code/petri_stage0.m < /dev/null     # 11T6, member 1
//   magma -b which:=11T1 Code/petri_stage0.m < /dev/null     # the §7 controls
//   magma -b prec:=40 which:=11T5 members:=2 Code/petri_stage0.m < /dev/null
//
// which:   11T1 -- the two closed-form curves of §7 as controls:
//                  (1,1,9) hyperelliptic, (1,2,8) trigonal (3 quadrics + 2 cubics)
//          11T5 -- PSL(2,11), passport size 2 (default: both members)
//          11T6 -- M11, passport size 30 (default: member 1)
//          11T7 -- A11, passport size 54949 (give members explicitly)
//          13T1 -- genus 6 controls: (1,1,11) hyperelliptic, (1,2,10) trigonal, (1,3,9) the Klein quintic
// members: comma-separated indices into the passport (PassportRepresentatives(G : genus := genus))
// genus:   expected genus, default 5 (used only to pick the passport); any dTt works
// triples: a file "triples := [ [* t, [[Eltseq(s0), Eltseq(s1), Eltseq(soo)], ...] *], ... ];"
//          to read the passport from instead of recomputing it (e.g. degree 13, genus 6 from a server)
// prec:    working precision, default 30
// al:      PowerSeriesBasis algorithm; default CArnoldi if the C solver is found, else Arnoldi
// skdir:   directory for per-member series checkpoints (reused when present)
//
// For each member it (1) runs the series stage, reporting its time and the
// absolute precision of the series; (2) runs TriangleHyperellipticTest FIRST
// on that Sk -- petri.m assumes hyperelliptic curves never reach it; (3) runs
// TrianglePetriTest(Sk, Gamma), whose verbose lines report the columns
// available against the columns wanted at each degree: the first measurement
// of series length against ideal size at degree 11.
//
// Sign convention: Magma composes left to right, so sigma_0 sigma_1 sigma_oo
// = 1 is &*Reverse(sigma) eq 1, as in belyi_9T25.m.

SetColumns(0);
AttachSpec("~/github/Belyi/Code/spec");
SetVerbose("Shimura", 1);
SetSeed(1);   // PassportRepresentatives is not deterministic across sessions; fix the member order

prec := assigned prec select StringToInteger(prec) else 30;
which := assigned which select which else "11T5";
members := assigned members select [StringToInteger(s) : s in Split(members, ",")] else [];

cbin := GetEnv("POWSER_ARNOLDI_BIN");
if cbin eq "" then cbin := "powser_arnoldi"; end if;
retc := System(Sprintf("command -v %o > /dev/null 2>&1 || test -x %o", cbin, cbin));
powseral := (retc eq 0) select "CArnoldi" else "Arnoldi";
if assigned al then powseral := al; end if;   // al:=Arnoldi forces the pure-Magma branch
printf "PowserAl := %o, prec := %o, which := %o\n", powseral, prec, which;

S11 := Sym(11);
s := S11!(1,2,3,4,5,6,7,8,9,10,11);
if which eq "11T1" then
  // exponents (1,1,9) and (1,2,8): s * s * s^9 = s * s^2 * s^8 = 1
  sigmas := [[s, s, s^9], [s, s^2, s^8]];
  labels := ["11T1 (1,1,9): y^11 = x(1-x), hyperelliptic", "11T1 (1,2,8): y^11 = x(1-x)^2, trigonal"];
  if #members gt 0 then
    sigmas := [sigmas[i] : i in members];
    labels := [labels[i] : i in members];
  end if;
elif which eq "13T1" then
  // genus 6: the three curves of the C13 passport (spec §9), exponents
  // (1,1,11) hyperelliptic, (1,2,10) trigonal, (1,3,9) the Klein quintic
  // x^4 y + y^4 z + z^4 x; the classifier reports both of the latter as
  // "Exceptional" with 6 quadrics and 3 cubics
  S13 := Sym(13);
  s13 := S13!(1,2,3,4,5,6,7,8,9,10,11,12,13);
  sigmas := [[s13, s13, s13^11], [s13, s13^2, s13^10], [s13, s13^3, s13^9]];
  labels := ["13T1 (1,1,11): y^13 = x(1-x), hyperelliptic",
             "13T1 (1,2,10): y^13 = x(1-x)^2, trigonal",
             "13T1 (1,3,9): y^13 = x(1-x)^3 = the Klein quintic, smooth plane quintic"];
  if #members gt 0 then
    sigmas := [sigmas[i] : i in members];
    labels := [labels[i] : i in members];
  end if;
else
  // which := dTt: degree d and transitive-group index t from the name;
  // genus := g (default 5); triples := <file> reads the passport from a file
  // written as "triples := [ [* t, [ [Eltseq(s0), Eltseq(s1), Eltseq(soo)], ... ] *], ... ];"
  // (the format the degree-11 dump used), so that a long PassportRepresentatives
  // run on a server need not be repeated here
  Tpos := Index(which, "T");
  error if Tpos lt 2, "which should look like 11T6";
  dd := StringToInteger(which[1..Tpos-1]);
  t := StringToInteger(which[Tpos+1..#which]);
  gen := assigned genus select StringToInteger(genus) else 5;
  Sd := Sym(dd);
  if assigned triples then
    // the file is a STATEMENT "triples := [...];", and eval wants an expression:
    // take what follows the ":=" up to the last "]"
    txt := Read(triples);
    i0 := Index(txt, ":=");
    error if i0 eq 0, "the triples file should contain \"triples := [ ... ];\"";
    i1 := Max([i : i in [1..#txt] | txt[i] eq "]"]);
    tr := eval txt[i0+2..i1];
    blocks := [b : b in tr | b[1] eq t];
    error if #blocks ne 1, Sprintf("the triples file has %o blocks for %o, expected 1", #blocks, which);
    allsig := [[Sd | Sd!s : s in sig] : sig in blocks[1][2]];
    printf "%o: %o triples read from %o\n", which, #allsig, triples;
  else
    G := TransitiveGroup(dd, t);
    P := PassportRepresentatives(G : genus := gen);
    error if #P ne 1, Sprintf("%o has %o passports of genus %o, expected exactly 1 (write them to a file and pass triples:=)", which, #P, gen);
    allsig := P[1][2];
    printf "%o: order %o, one genus-%o passport of size %o\n", which, #G, gen, #allsig;
  end if;
  if #members eq 0 then
    members := (which eq "11T5") select [1..#allsig] else [1];
  end if;
  sigmas := [allsig[i] : i in members];
  labels := [Sprintf("%o member %o of %o", which, i, #allsig) : i in members];
end if;

for k in [1..#sigmas] do
  sigma := sigmas[k];
  printf "\n=== %o ===\n%o\n", labels[k], sigma;
  Sdeg := Parent(sigma[1]);
  error if &*Reverse(sigma) ne Id(Sdeg), "the triple does not multiply to 1";
  error if not IsTransitive(sub<Sdeg | sigma>), "the triple is not transitive";
  Gamma := TriangleSubgroup(sigma);
  gg := Genus(Gamma);
  error if gg lt 5, Sprintf("genus %o: the Petri test is for genus >= 5", gg);
  Gamma`TriangleNumericalPrecision := prec;
  _ := UnitDisc(Gamma : Precision := prec);

  // skdir:=<dir> checkpoints the series stage per member (WriteObject), and
  // reuses the checkpoint if present: the series stage is the whole cost
  skfile := assigned skdir select Sprintf("%o/stage0_Sk_%o_member%o_p%o.obj", skdir, which, (#members gt 0 select members[k] else k), prec) else "";
  loaded := false;
  if skfile ne "" then
    try
      F := Open(skfile, "r"); Sk := ReadObject(F); delete F;
      loaded := true;
      printf "series stage: loaded %o\n", skfile;
    catch err
      loaded := false;
    end try;
  end if;
  if not loaded then
    t0 := Cputime();
    Sk := PowerSeriesBasis(Gamma, 2 : prec := prec, Federalize := true, Al := powseral);
    printf "series stage: %o s; %o forms; absolute precisions %o\n",
        Cputime(t0), #Sk, [AbsolutePrecision(f[1]) : f in Sk];
    if skfile ne "" then
      F := Open(skfile, "w"); WriteObject(F, Sk); delete F;
      printf "series stage: checkpointed to %o\n", skfile;
    end if;
  end if;

  // one member's failure must not abort the others: report it as the verdict
  try
    t0 := Cputime();
    hyp := TriangleHyperellipticTest(Sk, Gamma);
    printf "TriangleHyperellipticTest: %o (%o s)\n", hyp, Cputime(t0);
    if hyp then
      printf "VERDICT %o: HYPERELLIPTIC\n", labels[k];
    else
      t0 := Cputime();
      pc, Q, Cb := TrianglePetriTest(Sk, Gamma);
      printf "VERDICT %o: Petri case %o, %o quadrics, %o cubics (%o s)\n", labels[k], pc, #Q, #Cb, Cputime(t0);
    end if;
  catch err
    printf "VERDICT %o: ERROR at prec %o -- %o\n", labels[k], prec, err`Object;
  end try;
end for;
