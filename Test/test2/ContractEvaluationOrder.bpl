// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure P() returns (x, y: int)
  ensures x == y;  // ensured by the body
  ensures x == 0;  // error: not ensured by the body
  ensures y == 0;  // follows from the previous two ensures clauses (provided they are
                   // indeed evaluated in this order, which they are supposed to be)
{
  x := y;
}

procedure Q() returns (x, y: int)
{
  x := y;

  assert x == y;  // ensured by the body
  assert x == 0;  // error: not ensured by the body
  assert y == 0;  // follows from the previous two asserts (provided they are
                  // indeed evaluated in this order, which they are supposed to be)
}

procedure R()
{
  var a, b: int;
  a := b;
  call S(a, b);
}

procedure S(x, y: int)
                    // In the call from R:
  requires x == y;  // ensured by the body of R
  requires x == 0;  // error: not ensured by the body of R
  requires y == 0;  // follows from the previous two requires clauses (provided they are
                    // indeed evaluated in this order, which they are supposed to be)
{
}
