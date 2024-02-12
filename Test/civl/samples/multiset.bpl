// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X;

const unique null : int;
const unique nil: X;
const unique done: X;

var {:layer 0,3} elt : [int]int;
var {:layer 0,3} valid : [int]bool;
var {:layer 0,3} lock : [int]X;
var {:layer 0,3} owner : [int]X;
const max : int;

axiom (max > 0);

right action {:layer 1,2} atomic_acquire(i : int, {:linear} tid: One X)
modifies lock;
{ assert 0 <= i && i < max; assert tid->val != nil && tid->val != done; assume lock[i] == nil; lock[i] := tid->val; }

yield procedure {:layer 0} acquire(i : int, {:linear} tid: One X);
refines atomic_acquire;

left action {:layer 1,2} atomic_release(i : int, {:linear} tid: One X)
modifies lock;
{ assert 0 <= i && i < max; assert lock[i] == tid->val; assert tid->val != nil && tid->val != done; lock[i] := nil; }

yield procedure {:layer 0} release(i : int, {:linear} tid: One X);
refines atomic_release;

both action {:layer 1} atomic_getElt(j : int, {:linear} tid: One X) returns (elt_j:int)
{ assert 0 <= j && j < max; assert tid->val != nil && tid->val != done; assert lock[j] == tid->val; elt_j := elt[j]; }

yield procedure {:layer 0} getElt(j : int, {:linear} tid: One X) returns (elt_j:int);
refines atomic_getElt;

both action {:layer 1} atomic_setElt(j : int, x : int, {:linear} tid: One X)
modifies elt, owner;
{ assert x != null && owner[j] == nil; assert 0 <= j && j < max; assert lock[j] == tid->val; assert tid->val != nil && tid->val != done; elt[j] := x; owner[j] := tid->val; }

yield procedure {:layer 0} setElt(j : int, x : int, {:linear} tid: One X);
refines atomic_setElt;

left action {:layer 1,2} atomic_setEltToNull(j : int, {:linear} tid: One X)
modifies elt, owner;
{ assert owner[j] == tid->val && lock[j] == tid->val; assert 0 <= j && j < max; assert !valid[j]; assert tid->val != nil  && tid->val != done; elt[j] := null; owner[j] := nil; }

yield procedure {:layer 0} setEltToNull(j : int, {:linear} tid: One X);
refines atomic_setEltToNull;

both action {:layer 1,2} atomic_setValid(j : int, {:linear} tid: One X)
modifies valid, owner;
{ assert 0 <= j && j < max; assert lock[j] == tid->val; assert tid->val != nil && tid->val != done; assert owner[j] == tid->val; valid[j] := true; owner[j] := done; }

yield procedure {:layer 0} setValid(j : int, {:linear} tid: One X);
refines atomic_setValid;

both action {:layer 1,2} atomic_isEltThereAndValid(j : int, x : int, {:linear} tid: One X) returns (fnd:bool)
{ assert 0 <= j && j < max; assert lock[j] == tid->val; assert tid->val != nil && tid->val != done; fnd := (elt[j] == x) && valid[j]; }

yield procedure {:layer 0} isEltThereAndValid(j : int, x : int, {:linear} tid: One X) returns (fnd:bool);
refines atomic_isEltThereAndValid;

right action {:layer 2} AtomicFindSlot(x : int, {:linear} tid: One X) returns (r : int)
modifies elt, owner;
{
  assert tid->val != nil && tid->val != done;
  assert x != null;
  if (*) {
    assume (0 <= r && r < max);
    assume elt[r] == null;
    assume owner[r] == nil;
    assume !valid[r];
    elt[r] := x;
    owner[r] := tid->val;
  } else {
    assume (r == -1);
  }
}

yield procedure {:layer 1}
FindSlot(x : int, {:linear} tid: One X) returns (r : int)
refines AtomicFindSlot;
requires {:layer 1} x != null && tid->val != nil && tid->val != done;
preserves call Yield1();
{
  var j : int;
  var elt_j : int;

  par Yield1();

  j := 0;
  while(j < max)
  invariant {:yields} true;
  invariant call Yield1();
  invariant {:layer 1} 0 <= j;
  {
    call acquire(j, tid);
    call elt_j := getElt(j, tid);
    if(elt_j == null)
    {
      call setElt(j, x, tid);
      call release(j, tid);
      r := j;

      par Yield1();
      return;
    }
    call release(j,tid);

    par Yield1();

    j := j + 1;
  }
  r := -1;

  par Yield1();
  return;
}

atomic action {:layer 3} AtomicInsert(x : int, {:linear} tid: One X) returns (result : bool)
modifies elt, valid, owner;
{
  var r:int;
  if (*) {
    assume (0 <= r && r < max);
    assume valid[r] == false;
    assume elt[r] == null;
    assume owner[r] == nil;
    elt[r] := x;
    valid[r] := true;
    owner[r] := done;
    result := true;
  } else {
    result := false;
  }
}

yield procedure {:layer 2}
Insert(x : int, {:linear} tid: One X) returns (result : bool)
refines AtomicInsert;
requires {:layer 1,2} x != null && tid->val != nil && tid->val != done;
preserves call Yield1();
preserves call Yield2();
{
  var i: int;
  par Yield1() | Yield2();
  call i := FindSlot(x, tid);

  if(i == -1)
  {
    result := false;
    par Yield1() | Yield2();
    return;
  }
  par Yield1();
  assert {:layer 1} i != -1;
  assert {:layer 2} i != -1;
  call acquire(i, tid);
  assert {:layer 2} elt[i] == x;
  assert {:layer 2}  valid[i] == false;
  call setValid(i, tid);
  call release(i, tid);
  result := true;
  par Yield1() | Yield2();
  return;
}

atomic action {:layer 3} AtomicInsertPair(x : int, y : int, {:linear} tid: One X) returns (result : bool)
modifies elt, valid, owner;
{
  var rx:int;
  var ry:int;
  if (*) {
    assume (0 <= rx && rx < max && 0 <= ry && ry < max && rx != ry);
    assume valid[rx] == false;
    assume valid[ry] == false;
    assume elt[rx] == null;
    assume elt[rx] == null;
    elt[rx] := x;
    elt[ry] := y;
    valid[rx] := true;
    valid[ry] := true;
    owner[rx] := done;
    owner[ry] := done;
    result := true;
  } else {
    result := false;
  }
}

yield procedure {:layer 2}
InsertPair(x : int, y : int, {:linear} tid: One X) returns (result : bool)
refines AtomicInsertPair;
requires {:layer 1,2} x != null && y != null && tid->val != nil && tid->val != done;
preserves call Yield1();
preserves call Yield2();
{
  var i : int;
  var j : int;
  par Yield1() | Yield2();

  call i := FindSlot(x, tid);

  if (i == -1)
  {
    result := false;
    par Yield1() | Yield2();
    return;
  }

  par Yield1();
  call j := FindSlot(y, tid);

  if(j == -1)
  {
    par Yield1();
    call acquire(i,tid);
    call setEltToNull(i, tid);
    call release(i,tid);
    result := false;
    par Yield1() | Yield2();
    return;
  }

  par Yield1();
  assert {:layer 2} i != -1 && j != -1;
  call acquire(i, tid);
  call acquire(j, tid);
  assert {:layer 2} elt[i] == x;
  assert {:layer 2} elt[j] == y;
  assert {:layer 2}  valid[i] == false;
  assert {:layer 2}  valid[j] == false;
  call setValid(i, tid);
  call setValid(j, tid);
  call release(j, tid);
  call release(i, tid);
  result := true;
  par Yield1() | Yield2();
  return;
}

atomic action {:layer 3} AtomicLookUp(x : int, {:linear} tid: One X, old_valid:[int]bool, old_elt:[int]int) returns (found : bool)
{
  assert tid->val != nil && tid->val != done;
  assert x != null;
  assume found ==> (exists ii:int :: 0 <= ii && ii < max && valid[ii] && elt[ii] == x);
  assume !found ==> (forall ii:int :: 0 <= ii && ii < max ==> !(old_valid[ii] && old_elt[ii] == x));
}

yield procedure {:layer 2}
LookUp(x : int, {:linear} tid: One X, old_valid:[int]bool, old_elt:[int]int) returns (found : bool)
refines AtomicLookUp;
requires {:layer 1} {:layer 2} (tid->val != nil && tid->val != done);
preserves call Yield1();
preserves call Yield2();
preserves call YieldLookUp1(old_valid, old_elt);
preserves call YieldLookUp2(old_valid, old_elt);
{
  var j : int;
  var isThere : bool;

  par Yield1() | Yield2() | YieldLookUp1(old_valid, old_elt) | YieldLookUp2(old_valid, old_elt);

  j := 0;

  while(j < max)
  invariant {:yields} true;
  invariant call Yield1();
  invariant call Yield2();
  invariant call YieldLookUp1(old_valid, old_elt);
  invariant call YieldLookUp2(old_valid, old_elt);
  invariant {:layer 1} {:layer 2} (forall ii:int :: 0 <= ii && ii < j ==> !(old_valid[ii] && old_elt[ii] == x));
  invariant {:layer 1} {:layer 2} 0 <= j;
  {
    call acquire(j, tid);
    call isThere := isEltThereAndValid(j, x, tid);
    if(isThere)
    {
      call release(j, tid);
      found := true;
      par Yield1() | Yield2() | YieldLookUp1(old_valid, old_elt) | YieldLookUp2(old_valid, old_elt);
      return;
    }
    call release(j,tid);
    par Yield1() | Yield2() | YieldLookUp1(old_valid, old_elt) | YieldLookUp2(old_valid, old_elt);
    j := j + 1;
  }
  found := false;

  par Yield1() | Yield2() | YieldLookUp1(old_valid, old_elt) | YieldLookUp2(old_valid, old_elt);
  return;
}

yield invariant {:layer 1} Yield1();
invariant Inv(valid, elt, owner);

yield invariant {:layer 2} Yield2();
invariant Inv(valid, elt, owner);

function {:inline} Inv(valid: [int]bool, elt: [int]int, owner: [int]X): (bool)
{
  (forall i:int :: 0 <= i && i < max ==> (elt[i] == null <==> (!valid[i] && owner[i] == nil)))
}

yield invariant {:layer 1} YieldLookUp1(old_valid: [int]bool, old_elt: [int]int);
invariant InvLookUp(old_valid, valid, old_elt, elt);

yield invariant {:layer 2} YieldLookUp2(old_valid: [int]bool, old_elt: [int]int);
invariant InvLookUp(old_valid, valid, old_elt, elt);

function InvLookUp(old_valid: [int]bool, valid: [int]bool, old_elt: [int]int, elt: [int]int): (bool)
{
  (forall ii:int :: 0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii])
}
