// RUN: %boogie -proverWarnings:1 "%s" | %OutputCheck "%s"

function {:builtin "fp.abs RNA"} ABS(float24e8) returns (float24e8);
function {:builtin "fp.leq"} LEQ(rmode, float24e8, float24e8) returns (bool);

procedure foo()
{
  var r : rmode;
  var a : float24e8;
  var b : float24e8;

  a := 0x1.0e0f24e8;
  b := 0x1.0e0f24e8;

  // CHECK: Prover error: line \d+ column \d+: invalid number of arguments to floating point operator
  a := ABS(a);

  if (LEQ(RNA, a, b)) {
    a := b;
  }
}

// CHECK-L: Boogie program verifier finished with 0 verified, 0 errors
