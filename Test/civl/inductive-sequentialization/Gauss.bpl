// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x:int;

type {:pending_async}{:datatype} PA;
function {:constructor} ADD(i: int) : PA;

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 1}
{:IS "MAIN'","INV"}{:elim "ADD"}
SUM (n: int)
returns ({:pending_async "ADD"} PAs:[PA]int)
modifies x;
{
  assert
    {:add_to_pool "A", 0}
    n >= 0;
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
  var {:pool "A"} i: int;

  assert n >= 0;

  assume
    {:add_to_pool "A", i, i+1}
    {:add_to_pool "B", ADD(n)}
    0 <= i && i <= n;
  x := x + (i * (i+1)) div 2;
  PAs := (lambda {:pool "B"} pa: PA :: if is#ADD(pa) && i < i#ADD(pa) && i#ADD(pa) <= n then 1 else 0);
  choice := ADD(i+1);
}

////////////////////////////////////////////////////////////////////////////////

procedure {:left}{:layer 1}
ADD (i: int)
modifies x;
{
  x := x + i;
}
