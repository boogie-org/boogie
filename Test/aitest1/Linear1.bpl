// Simple test file for checking the inference of linear constraints.

var x: int;
var y: int;

procedure p()
{
  start:
    assume x*x == y;  // not a linear condition
    return;
}
