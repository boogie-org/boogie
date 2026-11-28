// A solver that rejects a command has not died, so the check is inconclusive.
// RUN: %boogie "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Verification inconclusive (P)
// CHECK-L: Boogie program verifier finished with 0 verified, 0 errors, 1 inconclusive

function {:bvbuiltin "no_such_op"} F(x: bv8) returns (bv8);

procedure P(x: bv8) {
  assert F(x) == x;
}
