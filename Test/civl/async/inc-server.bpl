// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ###########################################################################
// Linear permissions

function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;

function {:inline} {:linear "lin"} LinCollector(x : int) : [int]bool
{ MapConstBool(false)[x := true] }

function {:inline} perm (p : int) : bool
{ p == 0 }

// ###########################################################################
// Global shared variables

var {:layer 7,11} x : int;
var {:layer 7,11} y : int;

// ###########################################################################
// Main

procedure {:yields}{:layer 11} main ({:linear_in "lin"} p : int)
requires {:layer 9} perm(p) && x == y;
{
  yield; assert {:layer 9} perm(p) && x == y;
  async call Server_Inc(p);
  yield;
}

// ###########################################################################
// Event Handlers

procedure {:left}{:layer 10,11} inc_x_high_atomic ({:linear_in "lin"} p : int)
modifies x;
{ x := x + 1; }

procedure {:yields}{:layer 10}{:refines "inc_x_high_atomic"} Server_Inc ({:linear_in "lin"} p : int)
requires {:layer 9} perm(p) && x == y;
{
  yield; assert {:layer 9} perm(p) && x == y;
  async call AsyncInc(p);
  yield;
}

procedure {:yields}{:layer 9}{:refines "inc_x_high_atomic"} AsyncInc ({:linear_in "lin"} p : int)
requires {:layer 9} perm(p) && x == y;
{
  yield; assert {:layer 9} perm(p) && x == y;
  call inc_x_perm(p);
  async call Client_IncDone(p);
  yield;
}

// ###########################################################################
// Abstracted low-level atomic actions (i.e., enriched with permissions)

procedure {:atomic}{:layer 9} inc_x_perm_atomic ({:linear "lin"} p : int)
modifies x;
{ assert perm(p); x := x + 1; }

procedure {:left}{:layer 9} Client_IncDone_atomic ({:linear_in "lin"} p : int)
{ assert perm(p) && x == y + 1; }

procedure {:yields}{:layer 8}{:refines "inc_x_perm_atomic"} inc_x_perm ({:linear "lin"} p : int)
{
  yield;
  call inc_x();
  yield;
}

procedure {:yields}{:layer 8}{:refines "Client_IncDone_atomic"} Client_IncDone ({:linear_in "lin"} p : int)
{
  yield;
  call Assertion();
  yield;
}

// ###########################################################################
// Low-level atomic actions

procedure {:atomic}{:layer 8} inc_x_atomic ()
modifies x;
{ x := x + 1; }

procedure {:atomic}{:layer 8} Assertion_atomic ()
{ assert x == y + 1; }

procedure {:yields}{:layer 7}{:refines "inc_x_atomic"} inc_x ();
procedure {:yields}{:layer 7}{:refines "Assertion_atomic"} Assertion ();
