// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const n:int;
axiom n > 0;

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 1} {:pending_async} A () {}
procedure {:atomic}{:layer 1} {:pending_async} B () {}

procedure {:left}{:layer 1} {:creates "A"} C ()
{
  call create_async(A());
  // create undeclared pending async to B
  call create_async(B());
}

procedure {:left}{:layer 1} {:creates "A", "B"} D ()
{
  // do nothing
}
