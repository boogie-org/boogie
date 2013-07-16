var x: int;
var y: int;

procedure {:entrypoint} foo() 
{
  assume x == y;
  x := x + 1;
  async call P();
  y := y + 1;
}

procedure P()
requires x != y;
{
  assert x != y;
}