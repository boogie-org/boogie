// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:int;

yield left procedure {:layer 1} main (n: int)
requires {:layer 1} n >= 0;
ensures {:layer 1} x == old(x) + (n * (n+1)) div 2;
modifies x;
{
  var i: int;

  i := 0;
  while (i <= n)
  invariant {:layer 1} x == old(x) + (i * (i+1)) div 2;
  {
    async call {:sync} add(i);
  }
}

yield procedure {:layer 0} add (i: int);
refines left action {:layer 1} _ {
  x := x + i;
}
