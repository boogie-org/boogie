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

procedure {:yields} {:layer 1,2} Alloc({:linear "tid"} tid: X) returns (r: int)
ensures {:atomic} |{A: assert tid != nil; goto B, C;
                    B: assume r == -1; return true;
		    C: assume 0 <= r && r < max && status[r]; status[r] := false; return true; }|;
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

procedure {:yields} {:layer 1,2} Free({:linear "tid"} tid: X, i: int)
ensures {:atomic} |{A: assert tid != nil; status[i] := true; return true; }|;
{
  yield;
  call acquire(tid, i);
  call Write(tid, i, true);
  call release(tid, i);
  yield;
}

procedure {:yields} {:layer 0,1} acquire({:linear "tid"} tid: X, i: int);
ensures {:right} |{A: assert tid != nil; assume l[i] == nil; l[i] := tid; return true; }|;

procedure {:yields} {:layer 0,1} release({:linear "tid"} tid: X, i: int);
ensures {:left} |{A: assert tid != nil; assert l[i] == tid; l[i] := nil; return true; }|;

procedure {:yields} {:layer 0,1} Read({:linear "tid"} tid: X, i: int) returns (val: bool);
ensures {:both} |{A: assert tid != nil; assert l[i] == tid; val := status[i]; return true; }|;

procedure {:yields} {:layer 0,1} Write({:linear "tid"} tid: X, i: int, val: bool);
ensures {:both} |{A: assert tid != nil; assert l[i] == tid; status[i] := val; return true; }|;
