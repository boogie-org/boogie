// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const N : int;
axiom N > 0;

// ###########################################################################
// Global shared variables

var {:layer 0,1} x : int;

// ###########################################################################
// Main

yield procedure {:layer 1} main ()
{
  async call {:sync} inc_by_N();
  async call {:sync} dec_by_N();
}

yield <- procedure {:layer 1} inc_by_N ()
modifies x;
ensures {:layer 1} x == old(x) + N;
{
  var i : int;

  i := 0;
  while (i != N)
  invariant {:layer 1} x == old(x) + i;
  {
    i := i + 1;
    async call {:sync} inc();
  }
}

yield <- procedure {:layer 1} dec_by_N ()
modifies x;
ensures {:layer 1} x == old(x) - N;
{
  var i : int;

  i := 0;
  while (i != N)
  invariant {:layer 1} x == old(x) - i;
  {
    i := i + 1;
    async call {:sync} dec();
  }
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
