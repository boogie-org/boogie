// RUN: %boogie -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x:int;

type {:pending_async}{:datatype} PA;
function {:pending_async "INC"}{:constructor} INC_PA() : PA;
function {:pending_async "DEC"}{:constructor} DEC_PA() : PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 1}
{:IS "MAIN'","INV"}{:elim "INC"}{:elim "DEC"}
MAIN ()
returns ({:pending_async "INC","DEC"} PAs:[PA]int)
{
  PAs := NoPAs()[INC_PA() := 1][DEC_PA() := 1];
}

procedure {:atomic}{:layer 2}
MAIN' ()
{
}

procedure {:IS_invariant}{:layer 1}
INV ()
returns ({:pending_async "INC","DEC"} PAs:[PA]int)
modifies x;
{
  PAs := NoPAs();
  if (*) { PAs[INC_PA()] := 1; } else { x := x + 1; }
  if (*) { PAs[DEC_PA()] := 1; } else { x := x - 1; }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:left}{:layer 1}
INC ()
modifies x;
{
  x := x + 1;
}

procedure {:left}{:layer 1}
DEC ()
modifies x;
{
  x := x - 1;
}
