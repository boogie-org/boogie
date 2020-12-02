// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ###########################################################################

var {:layer 0,2} x : int;

// ###########################################################################

procedure {:yields} {:layer 1} {:refines "atomic_inc_x"} main (n: int)
requires {:layer 1} n >= 0;
{
  call inc(n);
}

procedure {:yields} {:left} {:layer 1} {:cooperates}  inc (i : int)
modifies x;
requires {:layer 1} i >= 0;
ensures {:layer 1} x == old(x) + i;
{
  if (i > 0)
  {
    call inc_x(1);
    async call {:sync} inc(i-1);
  }
}

procedure {:both} {:layer 1,2} atomic_inc_x (n: int)
modifies x;
{ x := x + n; }

procedure {:yields} {:layer 0} {:refines "atomic_inc_x"} inc_x (n: int);
