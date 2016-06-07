var y: int;
var x: int;

procedure {:inline 1} bar() returns (b: bool)
modifies y;
{
  if (b) {
    y := y + 1;
  } else {
    y := y - 1;
  }
}

procedure {:inline 1} foo() 
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


procedure main() returns (b: bool)
requires x == y;
ensures !b ==> x == y+1;
ensures b ==> x+1 == y;
modifies x, y;
modifies y;
{
  call foo();
  assert x == y;
  call b := bar();
}
