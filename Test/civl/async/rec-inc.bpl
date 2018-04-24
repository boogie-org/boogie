// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ###########################################################################

var {:layer 0,2} x : int;

// ###########################################################################

procedure {:yields} {:layer 1} {:refines "atomic_inc_x"} main (n: int)
requires {:layer 1} n >= 0;
{
  yield;
  call inc(n);
  yield;
}

procedure {:yields} {:left} {:layer 1} {:terminates}  inc (i : int)
modifies x;
requires {:layer 1} i >= 0;
ensures {:layer 1} x == old(x) + i;
{
  if (i > 0)
  {
    call inc_x(1);
    async call inc(i-1);
  }

  call dummy();
}

procedure {:yields} {:layer 0} dummy ();

procedure {:both} {:layer 1,2} atomic_inc_x (n: int)
modifies x;
{ x := x + n; }

procedure {:yields} {:layer 0} {:refines "atomic_inc_x"} inc_x (n: int);
