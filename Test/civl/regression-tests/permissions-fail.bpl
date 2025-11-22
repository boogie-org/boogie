// RUN: %parallel-boogie /trustRefinement "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// flag /trustRefinement avoids duplicate error messages since the precondition of Lemma
// is checked during both invariant checking and refinement checking at layer 1

var {:linear} {:layer 0,1} A : Set (One int);

pure procedure Lemma (set: Set (One int), i: One int);
requires !Set_Contains(set, i);

datatype D { D1({:linear} x: One int), D2(x: One int) }

yield procedure {:layer 1} Proc1 ({:linear} d: D)
{
  call {:layer 1} Lemma(A, d->x);
}

datatype E { E({:linear} x: One int) }

yield procedure {:layer 1} Proc2 (e: E)
{
  call {:layer 1} Lemma(A, e->x);
}