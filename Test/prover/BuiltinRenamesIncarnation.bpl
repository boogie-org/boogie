// RUN: %boogie /contractInfer /proverLog:"%t.smt2" "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t.smt2" "%s"

// Under /contractInfer, which declares the program before it creates a prover, the incarnation that would be
// x@0 is named differently too.

function {:builtin "x@0"} x0(): int;
var x: int;

procedure P()
  modifies x;
{
  havoc x;
  assert x == 1;
}
// CHECK-L: (declare-fun x@0@@0 () Int)
