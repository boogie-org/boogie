// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x:int;

type {:pending_async}{:datatype} PA;
function {:constructor} ADD(i: int) : PA;

////////////////////////////////////////////////////////////////////////////////

function trigger(i: int) : bool { true }

procedure {:atomic}{:layer 1}
{:IS "MAIN'","INV"}{:elim "ADD"}
SUM (n: int)
returns ({:pending_async "ADD"} PAs:[PA]int)
modifies x;
{
  assert n >= 0;
  assert trigger(0); // base hint
  PAs := (lambda pa: PA :: if is#ADD(pa) && 1 <= i#ADD(pa) && i#ADD(pa) <= n then 1 else 0);
}

procedure {:atomic}{:layer 2}
MAIN' (n: int)
modifies x;
{
  assert n >= 0;
  x := x + (n * (n+1)) div 2;
}

procedure {:IS_invariant}{:layer 1}
INV (n: int)
returns ({:pending_async "ADD"} PAs:[PA]int, {:choice} choice:PA)
modifies x;
{
  var i: int;

  assert n >= 0;
  
  assume 0 <= i && i <= n;
  x := x + (i * (i+1)) div 2;
  PAs := (lambda pa: PA :: if is#ADD(pa) && i < i#ADD(pa) && i#ADD(pa) <= n then 1 else 0);
  choice := ADD(i+1);

  assume trigger(i);                // the pattern we hope Z3 to put as a trigger
  assume trigger(i+1);              // step hint
  assume i < n ==> PAs[ADD(n)] > 0; // conclusion hint
}

////////////////////////////////////////////////////////////////////////////////

procedure {:left}{:layer 1}
ADD (i: int)
modifies x;
{
  x := x + i;
}
