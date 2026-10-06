// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ###########################################################################
// Global shared variables

var {:layer 0,1} x : int;

// ###########################################################################
// Main

atomic action {:layer 2} skip () {}

yield procedure {:layer 1} Main ()
refines skip;
{
  var {:layer 1} old_x: int;

  call {:layer 1} old_x := Copy(x);
  while (*)
  invariant {:layer 1} x == old_x;
  {
    async call {:sync} inc();
    async call {:sync} dec();
  }
}

// ###########################################################################
// Low level atomic actions

yield procedure {:layer 0} inc ();
refines left action {:layer 1} inc_atomic
{ x := x + 1; }

yield procedure {:layer 0} dec ();
refines left action {:layer 1} dec_atomic
{ x := x - 1; }
