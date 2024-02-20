// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:linear} {:layer 0,1} A : Set int;

pure procedure Lemma (set: Set int, i: One int);
requires !Set_Contains(set, i->val);

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