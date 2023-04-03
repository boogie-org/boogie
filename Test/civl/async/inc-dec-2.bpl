// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const N : int;
axiom N > 0;

// ###########################################################################
// Global shared variables

var {:layer 0,1} x : int;

// ###########################################################################
// Main

action {:layer 2} skip () {}

yield procedure {:layer 1} Main ()
refines skip;
{
  var i : int;
  var {:layer 1} old_x: int;

  i := 0;
  call old_x := snapshot_x();
  while (i != N)
  invariant {:layer 1} x == old_x;
  {
    async call {:sync} inc();
    async call {:sync} dec();
    i := i + 1;
  }
}

link action {:layer 1} snapshot_x() returns (snapshot: int)
{
   snapshot := x;
}

// ###########################################################################
// Low level atomic actions

<- action {:layer 1} inc_atomic ()
modifies x;
{ x := x + 1; }

<- action {:layer 1} dec_atomic ()
modifies x;
{ x := x - 1; }

yield procedure {:layer 0} inc ();
refines inc_atomic;

yield procedure {:layer 0} dec ();
refines dec_atomic;
