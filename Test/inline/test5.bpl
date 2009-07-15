// test a case, where the inlined proc comes before the caller

procedure {:inline 2} foo()
  modifies x;
{
  x := x + 1;
}

var x:int;

procedure  bar()
  modifies x;
{
  x := 3;
  call foo();
  assert x == 4;
  call foo();
  assert x == 5;
}

