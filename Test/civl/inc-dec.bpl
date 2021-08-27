// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ###########################################################################
// Global shared variables

var {:layer 0,2} x : int;

// ###########################################################################
// Main

procedure {:yields} {:layer 1} main (N: int)
requires {:layer 1} N >= 0;
{
  async call {:sync} inc_by_N(N);
  async call {:sync} dec_by_N(N);
}

procedure {:yields} {:layer 1} {:left} inc_by_N (N: int)
modifies x;
requires {:layer 1} N >= 0;
ensures {:layer 1} x == old(x) + N;
{
  var i : int;

  i := 0;
  while (i != N)
  invariant {:layer 1} {:cooperates} true;
  invariant {:layer 1} x == old(x) + i;
  {
    i := i + 1;
    async call {:sync} inc();
  }
}

procedure {:yields} {:layer 1} {:left} dec_by_N (N: int)
modifies x;
requires {:layer 1} N >= 0;
ensures {:layer 1} x == old(x) - N;
{
  var i : int;

  i := 0;
  while (i != N)
  invariant {:layer 1} {:cooperates} true;
  invariant {:layer 1} x == old(x) - i;
  {
    i := i + 1;
    async call {:sync} dec();
  }
}

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
