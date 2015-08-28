var x: int;
var y: int;

procedure {:inline 1} bar()
modifies y;
{
  y := y + 1;
}

procedure {:inline 1} foo() 
modifies x, y;
{
  x := x + 1;
  call bar();
  call bar();
  x := x + 1;
}

procedure main()
requires x == y;
ensures x != y;
modifies x, y;
{
  call foo();
}

