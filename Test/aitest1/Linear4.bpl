// Simple test file for checking the inference of linear constraints.

var x: int;
var y: int;

procedure p()
  modifies x;
{
  A:
    assume x < y;
    goto B;
  B:
    x := x*x;
    return;
}
