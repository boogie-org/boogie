var g: int;

procedure A()
requires g == 0;
modifies g;
ensures g == 2;
{
  var x : int;
  x := 4;
  while (g < x) {
    g := g + 1;
    x := x - 1;
  }
  assert x == 2;
}

procedure B(j: int) returns (x: int)
{
  var i: int;
  var y: int;

  y := 0;
  i := 0;
  x := j;
  while (i < 100) {
     x := x + 1 + y;
     i := i + 1;
  }
  assert y == 0;
}
