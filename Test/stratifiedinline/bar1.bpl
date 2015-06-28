// RUN: %boogie -stratifiedInline:1 -vc:i "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var x: int;
var y: int;

procedure bar()
modifies y;
{
  y := y + 1;
}

procedure foo() 
modifies x, y;
{
  x := x + 1;
  call bar();
  call bar();
  x := x + 1;
}

procedure {:entrypoint} main()
modifies x, y;
{
  assume x == y;
  call foo();
  assume x == y;
}

