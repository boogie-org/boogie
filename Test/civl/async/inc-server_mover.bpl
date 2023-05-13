// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ###########################################################################
// Linear permissions

type {:linear "lin"} Perm = int;

function {:inline} perm (p : int) : bool
{ p == 0 }

// ###########################################################################
// Global shared variables

var {:layer 7,9} x : int;
var {:layer 7,9} y : int;

// ###########################################################################
// Main

yield procedure {:layer 9} main ({:linear_in "lin"} p : int)
requires call Yield_9(p);
{
  async call {:sync} Server_Inc(p);
}

yield invariant {:layer 9} Yield_9({:linear "lin"} p : int);
invariant perm(p) && x == y;

// ###########################################################################
// Event Handlers

yield left procedure {:layer 9} Server_Inc ({:linear_in "lin"} p : int)
requires {:layer 9} perm(p) && x == y;
ensures  {:layer 9} x == old(x) + 1;
modifies x;
{
  call Yield_8();
  async call {:sync} AsyncInc(p);
  call Yield_8();
}

yield left procedure {:layer 9} AsyncInc ({:linear_in "lin"} p : int)
requires {:layer 9} perm(p) && x == y;
ensures  {:layer 9} x == old(x) + 1;
modifies x;
{
  call Yield_8();
  call inc_x_perm(p);
  async call {:sync} Client_IncDone(p);
  call Yield_8();
}

yield invariant{:layer 8} Yield_8 ();

// ###########################################################################
// Abstracted low-level atomic actions (i.e., enriched with permissions)

left action {:layer 9} inc_x_perm_atomic ({:linear "lin"} p : int)
modifies x;
{ assert perm(p); x := x + 1; }

left action {:layer 9} Client_IncDone_atomic ({:linear_in "lin"} p : int)
{ assert perm(p) && x == y + 1; }

yield procedure {:layer 8} inc_x_perm ({:linear "lin"} p : int)
refines inc_x_perm_atomic;
{
  call inc_x();
}

yield procedure {:layer 8} Client_IncDone ({:linear_in "lin"} p : int)
refines Client_IncDone_atomic;
{
  call Assertion();
}

// ###########################################################################
// Low-level atomic actions

atomic action {:layer 8} inc_x_atomic ()
modifies x;
{ x := x + 1; }

atomic action {:layer 8} Assertion_atomic ()
{ assert x == y + 1; }

yield procedure {:layer 7} inc_x ();
refines inc_x_atomic;

yield procedure {:layer 7} Assertion ();
refines Assertion_atomic;
