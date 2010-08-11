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