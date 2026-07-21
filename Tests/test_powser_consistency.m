// Slow numerical regression test (RUNSLOW=1): the degree-7 example's
// weight-4 power series basis computed via Al := "Arnoldi" and
// Al := "CArnoldi" at 100 digits must agree as analytic functions to
// working precision, both must certify minsing below eps_thresh, and the
// echelonized bases must have exact pivot structure.
AttachSpec("Code/spec");

cbin := GetEnv("POWSER_ARNOLDI_BIN");
if cbin eq "" then cbin := "powser_arnoldi"; end if;
retc := System(Sprintf("command -v %o > /dev/null 2>&1 || test -x %o", cbin, cbin));
if retc ne 0 then
  print "SKIP: powser_arnoldi binary not found (set POWSER_ARNOLDI_BIN)";
  quit;
end if;

prec := 100;
sigma := [Sym(7) | (1,2,3,4)(5,6,7), (2,3)(4,5)(6,7), (1,5,6,4,2)];

G1 := TriangleSubgroup(sigma); _ := UnitDisc(G1 : Precision := prec);
G2 := TriangleSubgroup(sigma); _ := UnitDisc(G2 : Precision := prec);
k := 0;
while SkDimension(G1, k) lt 2 do k +:= 2; end while;

Sk1, ms1 := PowerSeriesBasis(G1, k : dim := 2, Al := "Arnoldi");
Sk2, ms2 := PowerSeriesBasis(G2, k : dim := 2, Al := "CArnoldi");

eps_thresh := RealField(30)!10^(-prec + 2*Floor(Log(prec)));
assert ms1 lt eps_thresh;
assert ms2 lt eps_thresh;

// exact echelon pivot structure: same leading exponents, unit pivots.
// NB do not use LeadingTerm on the raw series: echelonization cancels
// entries above the pivot only up to ~10^(-prec)-level remnants, and
// whether such a remnant survives before the pivot is rounding luck
// (observed: an |c| ~ 1e-101 remnant at n = 1 ahead of a pivot at n = 4).
// Find the pivot as the first coefficient above a threshold instead.
RR := RealField(30);
pivthresh := RR!10^(-prec+10);
leaddeg := function(f)
  n := Degree(LeadingTerm(f));
  nmax := AbsolutePrecision(f);
  while Abs(Coefficient(f, n)) lt pivthresh do
    n +:= 1;
    error if n ge nmax,
      "basis row is entirely below the pivot threshold";
  end while;
  return n;
end function;
for i in [1..#Sk1] do
  s1 := leaddeg(Sk1[i][1]);
  s2 := leaddeg(Sk2[i][1]);
  assert s1 eq s2;
  assert Abs(Coefficient(Sk1[i][1], s1) - 1) lt RR!1e-90;
  assert Abs(Coefficient(Sk2[i][1], s2) - 1) lt RR!1e-90;
end for;

// function-level agreement well inside the disc
CC := ComplexField(prec);
N := 1168;
w0 := CC!(3/10) + (CC!(1/7))*CC.1;
maxdiff := RR!0;
for i in [1..#Sk1] do
  for j in [1..#Sk1[i]] do
    v1 := &+[Coefficient(Sk1[i][j], n)*w0^n : n in [0..N]];
    v2 := &+[Coefficient(Sk2[i][j], n)*w0^n : n in [0..N]];
    d := RR!Abs(v1 - v2);
    if d gt maxdiff then maxdiff := d; end if;
  end for;
end for;
printf "max function-level difference between bases: %o\n", maxdiff;
assert maxdiff lt RR!1e-70;

print "ALL TESTS PASSED";
quit;
