// RUN: %parallel-boogie /trustRefinement "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// flag /trustRefinement avoids duplicate error messages since the inlined assert in P
// is checked during both invariant checking and refinement checking at layer 1

var {:layer 1,1} g:int;

pure procedure {:inline 1} P(x:int)
{
  assert x == 0;
}

yield procedure {:layer 1} Y(x:int)
{
  call {:layer 1} P(x);
  assert {:layer 1} x == 0;
}
