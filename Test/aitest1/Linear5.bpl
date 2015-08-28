// RUN: %boogie -infer:j -instrumentInfer:e -printInstrumented -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Simple test file for checking the inference of linear constraints.

var x: int;
var y: int;

procedure p()
  modifies x;
{
  A:
    assume -1 <= x;
    goto B, E;
  B:
    assume x < y;
    goto C, E;
  C:
    x := x*x;
    goto D, E;
  D:
    x := y;
    return;
  E:
    return;
}
