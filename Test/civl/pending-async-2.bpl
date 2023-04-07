// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const n:int;
axiom n > 0;

////////////////////////////////////////////////////////////////////////////////

async action {:layer 1} A () {}
async action {:layer 1} B () {}

<- action {:layer 1} C ()
creates A;
{
  call create_async(A());
  // create undeclared pending async to B
  call create_async(B());
}

<- action {:layer 1} D ()
creates A, B;
{
  // do nothing
}
