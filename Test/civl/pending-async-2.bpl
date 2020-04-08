// RUN: %boogie -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const n:int;
axiom n > 0;

type {:pending_async}{:datatype} PA;
function {:pending_async "A"}{:constructor} A_PA() : PA;
function {:pending_async "B"}{:constructor} B_PA() : PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 1} A () {}
procedure {:atomic}{:layer 1} B () {}

procedure {:left}{:layer 1} C () returns ({:pending_async "A"} PAs:[PA]int)
{
  // create undeclared pending async to B
  PAs := NoPAs()[A_PA() := 1][B_PA() := 1];
}

procedure {:left}{:layer 1} D () returns ({:pending_async "A","B"} PAs:[PA]int)
{
  // (nondeterministically) create negative pending asyncs
}
