// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 1} Proc0 ({:linear} x: One int, {:linear} y: One int)
{
  assert {:layer 1} x != y;
}

var {:linear} {:layer 0,1} A : Set int;

yield procedure {:layer 1} Proc1 ({:linear} i: One int)
{
  call {:layer 1} Lemma(A, i);
}

pure procedure Lemma (set: Set int, i: One int);
requires !Set_Contains(set, i->val);

datatype D { D1({:linear} x: One int), D2({:linear} x: One int) }

yield procedure {:layer 1} Proc2 ({:linear} d: D)
{
  call {:layer 1} Lemma(A, d->x);
}

datatype E { E({:linear} d: D) }

yield procedure {:layer 1} Proc3 ({:linear} e: E)
{
  call {:layer 1} Lemma(A, e->d->x);
}

datatype D' { X({:linear} x: One int), Y(x: One int) }

yield procedure {:layer 1} Proc4 ({:linear} d: D')
requires {:layer 1} d is X;
{
  call {:layer 1} Lemma(A, d->x);
}