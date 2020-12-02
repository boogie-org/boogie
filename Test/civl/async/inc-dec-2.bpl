// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const N : int;
axiom N > 0;

// ###########################################################################
// Global shared variables

var {:layer 0,1} x : int;

// ###########################################################################
// Main

procedure {:atomic} {:layer 2} skip () {}

procedure {:yields} {:layer 1} {:refines "skip"} Main ()
{
  var i : int;
  var {:layer 1} old_x: int;

  i := 0;
  call old_x := snapshot_x();
  while (i != N)
  invariant {:layer 1} {:cooperates} true;
  invariant {:layer 1} x == old_x;
  {
    async call {:sync} inc();
    async call {:sync} dec();
    i := i + 1;
  }
}

procedure {:intro} {:layer 1} snapshot_x() returns (snapshot: int)
{
   snapshot := x;
}

// ###########################################################################
// Low level atomic actions

procedure {:left} {:layer 1} inc_atomic ()
modifies x;
{ x := x + 1; }

procedure {:left} {:layer 1} dec_atomic ()
modifies x;
{ x := x - 1; }

procedure {:yields} {:layer 0} {:refines "inc_atomic"} inc ();
procedure {:yields} {:layer 0} {:refines "dec_atomic"} dec ();
