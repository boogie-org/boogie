const N : int;
axiom N > 0;

// ###########################################################################
// Global shared variables

var {:layer 0,1} x : int;

// ###########################################################################
// Main

procedure {:yields} {:layer 1} main ()
{
  yield;
  async call inc_by_N();
  async call dec_by_N();
  yield;
}

procedure {:yields} {:layer 1} {:left} inc_by_N ()
ensures {:layer 1} x == old(x) + N;
{
  var i : int;

  call dummy();
  
  i := 0;
  while (i != N)
  invariant {:layer 1} x == old(x) + i;
  invariant {:layer 1} {:terminates} true;    
  {
    i := i + 1;
    async call inc();
    call dummy();
  }

  call dummy();
}

procedure {:yields} {:layer 1} {:left} dec_by_N ()
ensures {:layer 1} x == old(x) - N;
{
  var i : int;

  call dummy();

  i := 0;
  while (i != N)
  invariant {:layer 1} x == old(x) - i;
  invariant {:layer 1} {:terminates} true;
  {
    i := i + 1;
    async call dec();
    call dummy();
  }

  call dummy();
}

procedure {:yields} {:layer 0} dummy ();

// ###########################################################################
// Low level atomic actions

procedure {:both} {:layer 1} atomic_inc ()
modifies x;
{ x := x + 1; }

procedure {:both} {:layer 1} atomic_dec ()
modifies x;
{ x := x - 1; }

procedure {:yields} {:layer 0} {:refines "atomic_inc"} inc ();

procedure {:yields} {:layer 0} {:refines "atomic_dec"} dec ();
