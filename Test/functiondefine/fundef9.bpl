// RUN: %boogie "%s" | %OutputCheck "%s"

// CHECK-L: Prover error: Function definition cycle detected: foo depends on foo2
function {:define} foo(x:int) returns(int)
  { foo2(x) + 1 }
function {:define} foo2(x:int) returns(int)
  { foo(x) + 2 }

procedure test(x:int) returns (r:int)
  ensures r > 0;
{
  if (foo(x) > 0) {
    r := foo2(x);
  } else {
    r := 1;
  }
}

// CHECK-L: Boogie program verifier finished with 0 verified, 0 errors, 1 inconclusive
