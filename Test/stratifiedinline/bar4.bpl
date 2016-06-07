// RUN: %boogie -stratifiedInline:1 -vc:i "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var y: int;
var x: int;

procedure bar() returns (b: bool)
modifies y;
{
  if (b) {
    y := y + 1;
  } else {
    y := y - 1;
  }
}

procedure foo() 
modifies x, y;
{
  var b: bool;

  call b := bar();
  if (b) {
    x := x + 1;
  } else {
    x := x - 1;
  }
}


procedure {:entrypoint} main() returns (b: bool)
modifies x, y;
{
  assume x == y;
  call foo();
  if (x == y) {
    call b := bar();
    assume (if b then x+1 != y else x != y+1);
  }
}
