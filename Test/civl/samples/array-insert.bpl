// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Insertion into a sorted array

type Tid;
const nil:Tid;

var {:layer 0,2} A:[int]int;
var {:layer 0,2} count:int;
var {:layer 0,2} lock:Tid;

function {:inline} sorted (A:[int]int, count:int) : bool
{ (forall i:int, j:int :: 0 <= i && i <= j && j < count ==> A[i] <= A[j]) }

atomic action {:layer 2} INSERT ({:linear} tid: One Tid, v:int)
modifies A, count;
{
  var idx:int; // index at which v is written
  var old_A: [int]int;

  assert count >= 0;
  assert sorted(A, count);

  assume 0 <= idx && idx <= count;
  assume (forall i:int :: 0 <= i && i < idx ==> A[i] < v);
  assume (forall i:int :: idx <= i && i < count ==> A[i] >= v);

  old_A := A;
  havoc A;

  assume (forall i:int :: i < idx ==> A[i] == old_A[i]);
  assume (forall i:int :: idx < i && i < count ==> A[i+1] == old_A[i]);
  assume (forall i:int :: count < i ==> A[i] == old_A[i]);
  assume A[idx] == v;

  count := count + 1;
}

yield procedure {:layer 1} insert ({:linear} tid: One Tid, v:int)
refines INSERT;
requires {:layer 1} tid->val != nil;
{
  var idx:int; // index at which v is written
  var j:int;   // loop counter used for shifting
  var a:int;   // value read from A
  var c:int;   // value read from count
  var {:layer 1} _A:[int]int;

  call {:layer 1} Assert(0 <= count);
  call {:layer 1} _A := Copy(A);
  call acquire(tid);

  idx := 0;
  call c := read_count(tid);
  call a := read_A(tid, idx);
  while (idx < c && a < v)
    invariant {:layer 1} 0 <= idx && idx <= count;
    invariant {:layer 1} a == A[idx];
    invariant {:layer 1} (forall i:int :: 0 <= i && i < idx ==> A[i] < v);
  {
    idx := idx + 1;
    call a := read_A(tid, idx);
  }
  j := c;
  while (idx < j)
    invariant {:layer 1} idx <= j && j <= count;
    invariant {:layer 1} (forall i:int :: i <= j ==> A[i] == _A[i]);
    invariant {:layer 1} (forall i:int :: j < i && i <= count ==> A[i] == _A[i-1]);
    invariant {:layer 1} (forall i:int :: count < i ==> A[i] == _A[i]);
  {
    call a := read_A(tid, j-1);
    call write_A(tid, j, a);
    j := j - 1;
  }
  call write_A(tid, idx, v);
  call write_count(tid, c+1);

  // let's see if we can prove that A is still sorted
  call {:layer 1} Assert(sorted(A, count));

  call release(tid);
}

// =============================================================================

yield procedure {:layer 0} read_A ({:linear} tid: One Tid, i:int) returns (v:int);
refines both action {:layer 1} READ_A
{
  assert tid->val != nil && lock == tid->val;
  v := A[i];
}

yield procedure {:layer 0} write_A ({:linear} tid: One Tid, i:int, v:int);
refines both action {:layer 1} WRITE_A
{
  assert tid->val != nil && lock == tid->val;
  A[i] := v;
}

yield procedure {:layer 0} read_count ({:linear} tid: One Tid) returns (c:int);
refines both action {:layer 1} READ_COUNT
{
  assert tid->val != nil && lock == tid->val;
  c := count;
}

yield procedure {:layer 0} write_count ({:linear} tid: One Tid, c:int);
refines both action {:layer 1} WRITE_COUNT
{
  assert tid->val != nil && lock == tid->val;
  count := c;
}

yield procedure {:layer 0} acquire ({:linear} tid: One Tid);
refines right action {:layer 1} ACQUIRE
{
  assert tid->val != nil;
  assume lock == nil;
  lock := tid->val;
}

yield procedure {:layer 0} release ({:linear} tid: One Tid);
refines left action {:layer 1} RELEASE
{
  assert tid->val != nil && lock == tid->val;
  lock := nil;
}
