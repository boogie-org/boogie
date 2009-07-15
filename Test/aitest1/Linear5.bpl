// Simple test file for checking the inference of linear constraints.

var x: int;
var y: int;

procedure p()
  modifies x;
{
  A:
    assume -1 <= x;
    goto B;
  B:
    assume x < y;
    goto C;
  C:
    x := x*x;
    goto D;
  D:
    x := y;
    return;
}
