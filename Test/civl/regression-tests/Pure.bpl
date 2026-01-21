// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

pure procedure A(a: int) returns (b: int);
requires false;
ensures b == a;

yield procedure {:layer 1} X1(a: int) returns ({:layer 1} b: int)
refines atomic action {:layer 2} _ { b := a; }
{
    call {:layer 1} b := A(a);
}

yield procedure {:layer 2} X2(a: int) returns ({:layer 1} b: int)
{
    call {:layer 1} b := A(a);
}

pure action B(x:int)
{
  assert x >= 0;
}

yield procedure {:layer 1} Y1(x:int)
refines atomic action {:layer 2} _ { assert x == 0; }
{
  call {:layer 1} B(x);
}

yield procedure {:layer 2} Y2(x:int)
{
  call {:layer 1} B(x);
}

