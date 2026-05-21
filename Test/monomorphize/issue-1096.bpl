// RUN: %parallel-boogie /lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Chained bitvector concatenation should work with /lib:base (issue #1096)

function test4(a:bv8, b:bv8, c:bv8, d:bv8) returns (bv32) {
  a ++ b ++ c ++ d
}

procedure P(a: bv8, b: bv8, c: bv8)
  ensures a ++ b ++ c == a ++ b ++ c;
{
}
