// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x:int;

type {:pending_async}{:datatype} PA;
function {:constructor} INC() : PA;
function {:constructor} DEC() : PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 1}
{:IS "MAIN'","INV"}{:elim "INC"}{:elim "DEC"}
MAIN ()
returns ({:pending_async "INC","DEC"} PAs:[PA]int)
{
  PAs := NoPAs()[INC() := 1][DEC() := 1];
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
  if (*) { PAs[INC()] := 1; } else { x := x + 1; }
  if (*) { PAs[DEC()] := 1; } else { x := x - 1; }
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
