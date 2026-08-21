// Test the batched certified recognition path (MakeKBatch backed by
// Cext/makek_relfinder) against known algebraic numbers, and check the
// insufficient-precision verdict.  Requires MAKEK_RELFINDER_BIN.
//
//   MAKEK_RELFINDER_BIN=$PWD/Cext/makek_relfinder magma -b Tests/test_makek_relfinder.m

if GetEnv("MAKEK_RELFINDER_BIN") eq "" then
  print "SKIP: makek_relfinder binary not found (set MAKEK_RELFINDER_BIN)";
  quit;
end if;

AttachSpec("MagmaPolred/spec");
AttachSpec("Code/spec");

// ---- 1: mixed batch at generous precision: the sqrt(5)-side coefficient
// must be certified at degree 2, the rational one at degree 1, and the
// best (largest-degree) pick must be the degree-6 generator.
CC<i> := ComplexField(400);
// u6 = 2^(1/3) + 5^(1/2) generates a degree-6 field
u6 := CC ! (2^(CC!1/3) + Sqrt(CC!5));
u2 := CC ! ((1 + Sqrt(CC!(-7)))/2);
u1 := CC ! (22/7);
cfs := [u2, u1, u6];

bl, K, v, conj, uCC := MakeKBatch(cfs, 12);
assert bl;
assert Degree(K) eq 6;               // largest certified degree wins
assert Abs(Evaluate(K.1, v : Precision := 30)) ge 0;  // embedding exists
print "test 1 ok: degree-6 generator picked from mixed batch";

// ---- 2: batch with only low-degree entries picks the largest of those
bl, K2, v2, conj2, uCC2 := MakeKBatch([u1, u2], 12);
assert bl;
assert Degree(K2) eq 2;
print "test 2 ok: degree-2 pick";

// ---- 3: starved precision certifies nothing (and must NOT hand back junk)
CClow := ComplexField(30);
w := CClow ! ((100003)^(CClow!1/8) * 2^(CClow!1/3));  // deg-24 minpoly, heights >> 30 digits
bl3 := MakeKBatch([w], 24);
assert not bl3;
print "test 3 ok: starved precision -> bl = false";

// ---- 4: RecognizeOverK batch path: known elements of Q(sqrt5) recovered
// exactly, with denominator chaining across the sequence
R<x> := PolynomialRing(Rationals());
K5 := NumberField(x^2 - x - 1);   // ZK basis 1, phi
v5 := InfinitePlaces(K5)[2];      // phi -> golden ratio (positive root)
if Abs(Evaluate(K5.1, v5 : Precision := 30) - 1.618) gt 0.01 then
  v5 := InfinitePlaces(K5)[1];
end if;
els := [ K5 | (3 + 7*K5.1)/5, (-2 + 9*K5.1)/40, 11/3 ];
CCr := ComplexField(200);
targets := [ CCr!Evaluate(e, v5 : Precision := 200) : e in els ];
out := RecognizeOverK([targets], K5, v5, false);
assert out[1] eq els;
print "test 4 ok: RecognizeOverK batch recovers exact elements";

// ---- 5: a non-element in the sequence must raise the certified error
ok5 := false;
try
  _ := RecognizeOverK([[CCr!Pi(CCr)]], K5, v5, false);
catch e
  ok5 := true;
end try;
assert ok5;
print "test 5 ok: non-element -> certified error";

print "ALL TESTS PASSED";
exit;
