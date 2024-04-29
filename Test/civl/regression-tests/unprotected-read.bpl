// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Write (although lock-protected) is a non-mover, becaues of the unprotected
// read action ReadNoLock.

type Tid;
const nil:Tid;

var {:layer 0,1} lock:Tid;
var {:layer 0,1} x:int;

////////////////////////////////////////////////////////////////////////////////

right action {:layer 1} Acquire({:linear} tid: One Tid)
modifies lock;
{ assert tid->val != nil; assume lock == nil; lock := tid->val; }

left action {:layer 1} Release({:linear} tid: One Tid)
modifies lock;
{ assert tid->val != nil && lock == tid->val; lock := nil; }

atomic action {:layer 1} Write({:linear} tid: One Tid, val:int)
modifies x;
{ assert tid->val != nil && lock == tid->val; x := val; }

both action {:layer 1} ReadLock({:linear} tid: One Tid) returns (val:int)
{ assert tid->val != nil && lock == tid->val; val := x; }

atomic action {:layer 1} ReadNoLock() returns (val:int)
{ val := x; }
