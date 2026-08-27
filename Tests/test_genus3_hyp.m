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
X, phi := BelyiMap(Gamma : prec := 40, PowserAl := "CArnoldi");
assert BelyiMapSanityCheck(sigma, X, phi);
assert Gamma`TriangleIsHyperelliptic;
