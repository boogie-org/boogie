var x: int;
var y: int;

procedure {:inline 1} foo() 
{
  assert x == y;
}

procedure main()
requires x == y;
modifies x, y;
{
  x := x + 1;
  call foo();
}

