// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Write (although lock-protected) is a non-mover, becaues of the unprotected
// read action ReadNoLock.

type {:linear "tid"} Tid;
const nil:Tid;

var {:layer 0,1} lock:Tid;
var {:layer 0,1} x:int;

////////////////////////////////////////////////////////////////////////////////

-> action {:layer 1} Acquire({:linear "tid"} tid:Tid)
modifies lock;
{ assert tid != nil; assume lock == nil; lock := tid; }

<- action {:layer 1} Release({:linear "tid"} tid:Tid)
modifies lock;
{ assert tid != nil && lock == tid; lock := nil; }

action {:layer 1} Write({:linear "tid"} tid:Tid, val:int)
modifies x;
{ assert tid != nil && lock == tid; x := val; }

<-> action {:layer 1} ReadLock({:linear "tid"} tid:Tid) returns (val:int)
{ assert tid != nil && lock == tid; val := x; }

action {:layer 1} ReadNoLock() returns (val:int)
{ val := x; }
