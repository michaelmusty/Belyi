// hyperelliptic genus 3 map
// tests that TriangleHyperellipticTest is working
AttachSpec("Code/spec");

// 8T7-[8,8,4]-8-8-44-g3.m, pointed size 1
sigma := [Sym(8) | 
  (1, 2, 3, 4, 5, 6, 7, 8),
  (1, 6, 7, 4, 5, 2, 3, 8),
  (1, 3, 5, 7)(2, 8, 6, 4)
];
Gamma := TriangleSubgroup(sigma);

cbin := GetEnv("POWSER_ARNOLDI_BIN");
if cbin eq "" then cbin := "powser_arnoldi"; end if;
retc := System(Sprintf("command -v %o > /dev/null 2>&1 || test -x %o", cbin, cbin));
powseral := (retc eq 0) select "CArnoldi" else "Arnoldi";
printf "PowserAl := %o\n", powseral;

t0 := Cputime();
X, phi, Gamma := BelyiMap(Gamma : prec := 40, PowserAl := powseral);
printf "BelyiMap took %o s\n", Cputime(t0);

assert BelyiMapSanityCheck(sigma, X, phi);
assert Gamma`TriangleIsHyperelliptic;

print "ALL TESTS PASSED";
quit;
