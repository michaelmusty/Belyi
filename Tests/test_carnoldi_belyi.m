// End-to-end test of the external C solver path (PowserAl := "CArnoldi"),
// verified exactly against the ramification data.
AttachSpec("Code/spec");

// skip cleanly when the solver binary is not available
cbin := GetEnv("POWSER_ARNOLDI_BIN");
if cbin eq "" then cbin := "powser_arnoldi"; end if;
retc := System(Sprintf("command -v %o > /dev/null 2>&1 || test -x %o", cbin, cbin));
if retc ne 0 then
  print "SKIP: powser_arnoldi binary not found (set POWSER_ARNOLDI_BIN)";
  quit;
end if;

sigma := [Sym(4) | (1,2,3,4), (1,3,4,2), (1,3,4)];
X, phi := BelyiMap(sigma : PowserAl := "CArnoldi");
assert BelyiMapSanityCheck(sigma, X, phi);

// the two pipelines must produce the same exact map
sigma2 := [Sym(4) | (1,2,3,4), (1,3,4,2), (1,3,4)];
X2, phi2 := BelyiMap(sigma2);
assert Sprint(phi) eq Sprint(phi2);

print "ALL TESTS PASSED";
quit;
