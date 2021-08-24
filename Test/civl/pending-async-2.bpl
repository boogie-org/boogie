// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const n:int;
axiom n > 0;

type {:pending_async}{:datatype} PA;
function {:constructor} A() : PA;
function {:constructor} B() : PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 1} A () {}
procedure {:atomic}{:layer 1} B () {}

procedure {:left}{:layer 1} C () returns ({:pending_async "A"} PAs:[PA]int)
{
  // create undeclared pending async to B
  PAs := NoPAs()[A() := 1][B() := 1];
}

procedure {:left}{:layer 1} D () returns ({:pending_async "A","B"} PAs:[PA]int)
{
  // (nondeterministically) create negative pending asyncs
}
