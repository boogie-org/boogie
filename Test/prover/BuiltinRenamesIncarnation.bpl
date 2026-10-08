// RUN: %boogie "%s" /proverLog:"%t.smt2" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %OutputCheck --file-to-check "%t.smt2" "%s"
// RUN: %boogie /contractInfer "%s" /proverLog:"%t.houdini.smt2" > "%t.houdini"
// RUN: %OutputCheck --file-to-check "%t.houdini.smt2" "%s"

// The incarnation that would be x@0 is named differently, also under /contractInfer, and the error trace stays
// intact.

function {:builtin "x@0"} x0(): int;
var x: int;

procedure P()
  modifies x;
{
  havoc x;
  goto A, B;
  A:
    assume x > 0;
    goto C;
  B:
    assume x <= 0;
    goto C;
  C:
    assert x == 1;
}
// CHECK-L: (declare-fun x@0@@0 () Int)
