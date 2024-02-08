// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:linear} {:layer 0,1} A : Set int;

yield procedure {:layer 1} Proc ({:linear} i: One int)
{
  call {:layer 1} Lemma(A, i);
}

pure procedure Lemma (set: Set int, i: One int);
requires !Set_Contains(set, i->val);
