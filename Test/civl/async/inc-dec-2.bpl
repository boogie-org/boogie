// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
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

  yield; assert {:layer 1} x == old(x);
  
  i := 0;
  while (i != N)
  invariant {:layer 1} x == old(x);
  invariant {:layer 1} {:terminates} true;    
  {
    async call inc();
    async call dec();
    i := i + 1;
    yield; assert {:layer 1} x == old(x);
  }

  yield;
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
