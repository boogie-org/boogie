// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ###########################################################################

var {:layer 0,2} x : int;

// ###########################################################################

yield procedure {:layer 1} main (n: int)
refines atomic_inc_x;
requires {:layer 1} n >= 0;
{
  call inc(n);
}

yield left procedure {:layer 1} inc (i : int)
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

both action {:layer 1,2} atomic_inc_x (n: int)
modifies x;
{ x := x + n; }

yield procedure {:layer 0} inc_x (n: int);
refines atomic_inc_x;
