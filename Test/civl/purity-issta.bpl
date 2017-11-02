// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X;
const nil: X;

function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}

const max: int;
axiom 0 <= max;

var {:layer 0,1} l: [int]X;
var {:layer 0,2} status: [int]bool;

procedure {:atomic} {:layer 2} atomic_Alloc({:linear "tid"} tid: X) returns (r: int)
modifies status;
{
  assert tid != nil;
  if (*) {
    assume r == -1;
  } else {
    assume 0 <= r && r < max && status[r];
    status[r] := false;
  }
}

procedure {:atomic} {:layer 2} atomic_Free({:linear "tid"} tid: X, i: int)
modifies status;
{ assert tid != nil; status[i] := true; }

procedure {:yields} {:layer 1} {:refines "atomic_Alloc"} Alloc({:linear "tid"} tid: X) returns (r: int)
{
  var i: int;
  var b: bool;

  i := 0;
  r := -1;
  while (i < max)
  invariant {:layer 1} 0 <= i;
  {
    yield;
    call acquire(tid, i);
    call b := Read(tid, i);
    if (b) {
      call Write(tid, i, false);
      call release(tid, i);
      r := i;
      break;
    }
    call release(tid, i);
    i := i + 1;
    yield;
  }
  yield;
}

procedure {:yields} {:layer 1} {:refines "atomic_Free"} Free({:linear "tid"} tid: X, i: int)
{
  yield;
  call acquire(tid, i);
  call Write(tid, i, true);
  call release(tid, i);
  yield;
}

procedure {:right} {:layer 1} atomic_acquire({:linear "tid"} tid: X, i: int)
modifies l;
{ assert tid != nil; assume l[i] == nil; l[i] := tid; }

procedure {:left} {:layer 1} atomic_release({:linear "tid"} tid: X, i: int)
modifies l;
{ assert tid != nil; assert l[i] == tid; l[i] := nil; }

procedure {:both} {:layer 1} atomic_Read({:linear "tid"} tid: X, i: int) returns (val: bool)
{ assert tid != nil; assert l[i] == tid; val := status[i]; }

procedure {:both} {:layer 1} atomic_Write({:linear "tid"} tid: X, i: int, val: bool)
modifies status;
{ assert tid != nil; assert l[i] == tid; status[i] := val; }

procedure {:yields} {:layer 0} {:refines "atomic_acquire"} acquire({:linear "tid"} tid: X, i: int);
procedure {:yields} {:layer 0} {:refines "atomic_release"} release({:linear "tid"} tid: X, i: int);
procedure {:yields} {:layer 0} {:refines "atomic_Read"} Read({:linear "tid"} tid: X, i: int) returns (val: bool);
procedure {:yields} {:layer 0} {:refines "atomic_Write"} Write({:linear "tid"} tid: X, i: int, val: bool);
