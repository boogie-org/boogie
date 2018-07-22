// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Write (although lock-protected) is a non-mover, becaues of the unprotected
// read action ReadNoLock.

type Tid;
const nil:Tid;

var {:layer 0,1} lock:Tid;
var {:layer 0,1} x:int;

////////////////////////////////////////////////////////////////////////////////

procedure {:right} {:layer 1} Acquire({:linear "tid"} tid:Tid)
modifies lock;
{ assert tid != nil; assume lock == nil; lock := tid; }

procedure {:left} {:layer 1} Release({:linear "tid"} tid:Tid)
modifies lock;
{ assert tid != nil && lock == tid; lock := nil; }

procedure {:atomic} {:layer 1} Write({:linear "tid"} tid:Tid, val:int)
modifies x;
{ assert tid != nil && lock == tid; x := val; }

procedure {:both} {:layer 1} ReadLock({:linear "tid"} tid:Tid) returns (val:int)
{ assert tid != nil && lock == tid; val := x; }

procedure {:atomic} {:layer 1} ReadNoLock() returns (val:int)
{ val := x; }

////////////////////////////////////////////////////////////////////////////////

function {:builtin "MapConst"} MapConstBool(bool) : [Tid]bool;
function {:inline} {:linear "tid"} TidCollector(tid:Tid) : [Tid]bool
{
  MapConstBool(false)[tid := true]
}
