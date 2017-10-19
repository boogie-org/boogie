// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
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

function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}

axiom (max > 0);

procedure {:right} {:layer 1,2} atomic_acquire(i : int, {:linear "tid"} tid: X)
modifies lock;
{ assert 0 <= i && i < max; assert tid != nil && tid != done; assume lock[i] == nil; lock[i] := tid; }

procedure {:yields} {:layer 0} {:refines "atomic_acquire"} acquire(i : int, {:linear "tid"} tid: X);

procedure {:left} {:layer 1,2} atomic_release(i : int, {:linear "tid"} tid: X)
modifies lock;
{ assert 0 <= i && i < max; assert lock[i] == tid; assert tid != nil && tid != done; lock[i] := nil; }

procedure {:yields} {:layer 0} {:refines "atomic_release"} release(i : int, {:linear "tid"} tid: X);

procedure {:both} {:layer 1} atomic_getElt(j : int, {:linear "tid"} tid: X) returns (elt_j:int)
{ assert 0 <= j && j < max; assert tid != nil && tid != done; assert lock[j] == tid; elt_j := elt[j]; }

procedure {:yields} {:layer 0} {:refines "atomic_getElt"} getElt(j : int, {:linear "tid"} tid: X) returns (elt_j:int);

procedure {:both} {:layer 1} atomic_setElt(j : int, x : int, {:linear "tid"} tid: X)
modifies elt, owner;
{ assert x != null && owner[j] == nil; assert 0 <= j && j < max; assert lock[j] == tid; assert tid != nil && tid != done; elt[j] := x; owner[j] := tid; }

procedure {:yields} {:layer 0} {:refines "atomic_setElt"} setElt(j : int, x : int, {:linear "tid"} tid: X);

procedure {:left} {:layer 1,2} atomic_setEltToNull(j : int, {:linear "tid"} tid: X)
modifies elt, owner;
{ assert owner[j] == tid && lock[j] == tid; assert 0 <= j && j < max; assert !valid[j]; assert tid != nil  && tid != done; elt[j] := null; owner[j] := nil; }

procedure {:yields} {:layer 0} {:refines "atomic_setEltToNull"} setEltToNull(j : int, {:linear "tid"} tid: X);

procedure {:both} {:layer 1,2} atomic_setValid(j : int, {:linear "tid"} tid: X)
modifies valid, owner;
{ assert 0 <= j && j < max; assert lock[j] == tid; assert tid != nil && tid != done; assert owner[j] == tid; valid[j] := true; owner[j] := done; }

procedure {:yields} {:layer 0} {:refines "atomic_setValid"} setValid(j : int, {:linear "tid"} tid: X);

procedure {:both} {:layer 1,2} atomic_isEltThereAndValid(j : int, x : int, {:linear "tid"} tid: X) returns (fnd:bool)
{ assert 0 <= j && j < max; assert lock[j] == tid; assert tid != nil && tid != done; fnd := (elt[j] == x) && valid[j]; }

procedure {:yields} {:layer 0} {:refines "atomic_isEltThereAndValid"} isEltThereAndValid(j : int, x : int, {:linear "tid"} tid: X) returns (fnd:bool);

procedure {:right} {:layer 2} AtomicFindSlot(x : int, {:linear "tid"} tid: X) returns (r : int)
modifies elt, owner;
{
  assert tid != nil && tid != done;
  assert x != null;
  if (*) {
    assume (0 <= r && r < max);
    assume elt[r] == null;
    assume owner[r] == nil;
    assume !valid[r];
    elt[r] := x;
    owner[r] := tid;
  } else {
    assume (r == -1);
  }
}

procedure {:yields} {:layer 1} {:refines "AtomicFindSlot"} FindSlot(x : int, {:linear "tid"} tid: X) returns (r : int)
requires {:layer 1} Inv(valid, elt, owner) && x != null && tid != nil && tid != done;
ensures {:layer 1} Inv(valid, elt, owner);
{
  var j : int;
  var elt_j : int;

  par Yield1();

  j := 0;
  while(j < max)
  invariant {:layer 1} Inv(valid, elt, owner);
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

procedure {:atomic} {:layer 3} AtomicInsert(x : int, {:linear "tid"} tid: X) returns (result : bool)
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

procedure {:yields} {:layer 2} {:refines "AtomicInsert"} Insert(x : int, {:linear "tid"} tid: X) returns (result : bool)
requires {:layer 1} Inv(valid, elt, owner) && x != null && tid != nil && tid != done;
ensures {:layer 1} Inv(valid, elt, owner);
requires {:layer 2} Inv(valid, elt, owner) && x != null && tid != nil && tid != done;
ensures {:layer 2} Inv(valid, elt, owner);
{
  var i: int;
  par Yield12();
  call i := FindSlot(x, tid);

  if(i == -1)
  {
    result := false;
    par Yield12();
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
  par Yield12();
  return;
}

procedure {:atomic} {:layer 3} AtomicInsertPair(x : int, y : int, {:linear "tid"} tid: X) returns (result : bool)
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

procedure {:yields} {:layer 2} {:refines "AtomicInsertPair"} InsertPair(x : int, y : int, {:linear "tid"} tid: X) returns (result : bool)
requires {:layer 1} Inv(valid, elt, owner) && x != null && y != null && tid != nil && tid != done;
ensures {:layer 1} Inv(valid, elt, owner);
requires {:layer 2} Inv(valid, elt, owner) && x != null && y != null && tid != nil && tid != done;
ensures {:layer 2} Inv(valid, elt, owner);
{
  var i : int;
  var j : int;
  par Yield12();

  call i := FindSlot(x, tid);

  if (i == -1)
  {
    result := false;
    par Yield12();
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
    par Yield12();
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
  par Yield12();
  return;
}

procedure {:atomic} {:layer 3} AtomicLookUp(x : int, {:linear "tid"} tid: X, old_valid:[int]bool, old_elt:[int]int) returns (found : bool)
{
  assert tid != nil && tid != done;
  assert x != null;
  assume found ==> (exists ii:int :: 0 <= ii && ii < max && valid[ii] && elt[ii] == x);
  assume !found ==> (forall ii:int :: 0 <= ii && ii < max ==> !(old_valid[ii] && old_elt[ii] == x));
}

procedure {:yields} {:layer 2} {:refines "AtomicLookUp"} LookUp(x : int, {:linear "tid"} tid: X, old_valid:[int]bool, old_elt:[int]int) returns (found : bool)
requires {:layer 1} {:layer 2} old_valid == valid && old_elt == elt;
requires {:layer 1} {:layer 2} Inv(valid, elt, owner);
requires {:layer 1} {:layer 2} (tid != nil && tid != done);
ensures {:layer 1} {:layer 2} Inv(valid, elt, owner);
{
  var j : int;
  var isThere : bool;

  par Yield12() | YieldLookUp(old_valid, old_elt);

  j := 0;

  while(j < max)
  invariant {:layer 1} {:layer 2} Inv(valid, elt, owner);
  invariant {:layer 1} {:layer 2} (forall ii:int :: 0 <= ii && ii < j ==> !(old_valid[ii] && old_elt[ii] == x));
  invariant {:layer 1} {:layer 2} (forall ii:int :: 0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
  invariant {:layer 1} {:layer 2} 0 <= j;
  {
    call acquire(j, tid);
    call isThere := isEltThereAndValid(j, x, tid);
    if(isThere)
    {
      call release(j, tid);
      found := true;
      par Yield12() | YieldLookUp(old_valid, old_elt);
      return;
    }
    call release(j,tid);
    par Yield12() | YieldLookUp(old_valid, old_elt);
    j := j + 1;
  }
  found := false;

  par Yield12() | YieldLookUp(old_valid, old_elt);
  return;
}

procedure {:yields} {:layer 1} Yield1()
requires {:layer 1} Inv(valid, elt, owner);
ensures {:layer 1} Inv(valid, elt, owner);
{
  yield;
  assert {:layer 1} Inv(valid, elt, owner);
}

procedure {:yields} {:layer 2} Yield12()
requires {:layer 1} {:layer 2} Inv(valid, elt, owner);
ensures {:layer 1} {:layer 2} Inv(valid, elt, owner);
{
  yield;
  assert {:layer 1} {:layer 2} Inv(valid, elt, owner);
}

function {:inline} Inv(valid: [int]bool, elt: [int]int, owner: [int]X): (bool)
{
  (forall i:int :: 0 <= i && i < max ==> (elt[i] == null <==> (!valid[i] && owner[i] == nil)))
}

procedure {:yields} {:layer 2} YieldLookUp(old_valid: [int]bool, old_elt: [int]int)
requires {:layer 1} {:layer 2} (forall ii:int :: 0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
ensures {:layer 1} {:layer 2} (forall ii:int :: 0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
{
  yield;
  assert {:layer 1} {:layer 2} (forall ii:int :: 0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
}
