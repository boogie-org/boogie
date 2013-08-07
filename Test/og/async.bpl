var x: int;
var y: int;

procedure {:entrypoint} {:yields} foo()
modifies x, y; 
{
  assume x == y;
  x := x + 1;
  async call P();
  y := y + 1;
}

procedure {:yields} {:stable} P()
requires x != y;
{
  assert x != y;
}