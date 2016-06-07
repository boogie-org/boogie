// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// The partition step of Quick Sort picks a 'pivot' element from a specified subsection
// of a given integer array.  It then partially sorts the elements of the array so that
// elements smaller than the pivot end up to the left of the pivot and elements larger
// than the pivot end up to the right of the pivot.  Finally, the index of the pivot is
// returned.
// The procedure below always picks the first element of the subregion as the pivot.
// The specification of the procedure talks about the ordering of the elements, but
// does not say anything about keeping the multiset of elements the same.

var A: [int]int;
const N: int;

procedure Partition(l: int, r: int) returns (result: int)
  requires 0 <= l && l+2 <= r && r <= N;
  modifies A;
  ensures l <= result && result < r;
  ensures (forall k: int, j: int :: l <= k && k < result && result <= j && j < r  ==>  A[k] <= A[j]);
  ensures (forall k: int :: l <= k && k < result  ==>  A[k] <= old(A)[l]);
  ensures (forall k: int :: result <= k && k < r  ==>  old(A)[l] <= A[k]);
{
  var pv, i, j, tmp: int;

  pv := A[l];
  i := l;
  j := r-1;
  // swap A[l] and A[j]
  tmp := A[l];
  A[l] := A[j];
  A[j] := tmp;
  goto LoopHead;

  // The following loop iterates while 'i < j'.  In each iteration,
  // one of the three alternatives (A, B, or C) is chosen in such
  // a way that the assume statements will evaluate to true.
  LoopHead:
    // The following the assert statements give the loop invariant
    assert (forall k: int :: l <= k && k < i  ==>  A[k] <= pv);
    assert (forall k: int :: j <= k && k < r  ==>  pv <= A[k]);
    assert l <= i && i <= j && j < r;
    goto A, B, C, exit;

  A:
    assume i < j;
    assume A[i] <= pv;
    i := i + 1;
    goto LoopHead;

  B:
    assume i < j;
    assume pv <= A[j-1];
    j := j - 1;
    goto LoopHead;

  C:
    assume i < j;
    assume A[j-1] < pv && pv < A[i];
    // swap A[j-1] and A[i]
    tmp := A[i];
    A[i] := A[j-1];
    A[j-1] := tmp;
    assert A[i] < pv && pv < A[j-1];
    i := i + 1;
    j := j - 1;
    goto LoopHead;

  exit:
    assume i == j;
    result := i;
}
