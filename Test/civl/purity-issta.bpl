// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "tid"} X;
const nil: X;

const max: int;
axiom 0 <= max;

var {:layer 0,1} l: [int]X;
var {:layer 0,2} status: [int]bool;

>-< action {:layer 2} atomic_Alloc({:linear "tid"} tid: X) returns (r: int)
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

>-< action {:layer 2} atomic_Free({:linear "tid"} tid: X, i: int)
modifies status;
{ assert tid != nil; status[i] := true; }

yield procedure {:layer 1} Alloc({:linear "tid"} tid: X) returns (r: int)
refines atomic_Alloc;
{
  var i: int;
  var b: bool;

  i := 0;
  r := -1;
  while (i < max)
  invariant {:yields} true;
  invariant {:layer 1} 0 <= i;
  {
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
  }
}

yield procedure {:layer 1} Free({:linear "tid"} tid: X, i: int)
refines atomic_Free;
{
  call acquire(tid, i);
  call Write(tid, i, true);
  call release(tid, i);
}

-> action {:layer 1} atomic_acquire({:linear "tid"} tid: X, i: int)
modifies l;
{ assert tid != nil; assume l[i] == nil; l[i] := tid; }

<- action {:layer 1} atomic_release({:linear "tid"} tid: X, i: int)
modifies l;
{ assert tid != nil; assert l[i] == tid; l[i] := nil; }

<-> action {:layer 1} atomic_Read({:linear "tid"} tid: X, i: int) returns (val: bool)
{ assert tid != nil; assert l[i] == tid; val := status[i]; }

<-> action {:layer 1} atomic_Write({:linear "tid"} tid: X, i: int, val: bool)
modifies status;
{ assert tid != nil; assert l[i] == tid; status[i] := val; }

yield procedure {:layer 0} acquire({:linear "tid"} tid: X, i: int);
refines atomic_acquire;

yield procedure {:layer 0} release({:linear "tid"} tid: X, i: int);
refines atomic_release;

yield procedure {:layer 0} Read({:linear "tid"} tid: X, i: int) returns (val: bool);
refines atomic_Read;

yield procedure {:layer 0} Write({:linear "tid"} tid: X, i: int, val: bool);
refines atomic_Write;
