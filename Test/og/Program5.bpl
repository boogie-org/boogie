// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type Tid;
const unique nil: Tid;
function {:builtin "MapConst"} MapConstBool(bool): [Tid]bool;
function {:builtin "MapOr"} MapOr([Tid]bool, [Tid]bool) : [Tid]bool;

var {:phase 0,3} Color:int;
var {:phase 0,3} lock:Tid;

function {:inline} {:linear "tid"} TidCollector(x: Tid) : [Tid]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [Tid]bool) : [Tid]bool
{
  x
}

function {:inline} UNALLOC():int { 0 }
function {:inline} WHITE():int { 1 }
function {:inline} GRAY():int { 2 }
function {:inline} BLACK():int { 3 }
function {:inline} Unalloc(i:int) returns(bool) { i <= 0 }
function {:inline} White(i:int) returns(bool) { i == 1 }
function {:inline} Gray(i:int) returns(bool) { i == 2 }
function {:inline} Black(i:int) returns(bool) { i >= 3 }

procedure {:yields} {:phase 0,1} AcquireLock({:linear "tid"} tid: Tid);
  ensures {:right} |{ A: assert tid != nil; 
                         assume lock == nil; 
                         lock := tid; 
                         return true; }|;

procedure {:yields} {:phase 0,1} ReleaseLock({:linear "tid"} tid: Tid);
  ensures {:left} |{ A: assert tid != nil;
                         assert lock == tid; 
                         lock := nil; 
                         return true; }|;

procedure {:yields} {:phase 0,1} SetColorLocked({:linear "tid"} tid:Tid, newCol:int); 
  ensures {:atomic} |{A: assert tid != nil; assert lock == tid; Color := newCol; return true;}|;

procedure {:yields} {:phase 0,1} GetColorLocked({:linear "tid"} tid:Tid) returns (col:int);
  ensures {:both} |{A: assert tid != nil; assert lock == tid; col := Color; return true;}|;

procedure {:yields} {:phase 1,2} GetColorNoLock() returns (col:int);
  ensures {:atomic} |{A: col := Color; return true;}|;

procedure {:yields} {:phase 2} YieldColorOnlyGetsDarker()
ensures {:phase 2} Color >= old(Color);
{
  yield;
  assert {:phase 2} Color >= old(Color);
}


procedure {:yields} {:phase 2,3} TopWriteBarrier({:linear "tid"} tid:Tid)
ensures {:atomic} |{ A: assert tid != nil;
                        goto B, C; 
                     B: assume White(Color);
                        Color := GRAY();
                        return true; 
                     C: return true;}|;
{
  var colorLocal:int;

  yield;

  call colorLocal := GetColorNoLock();
  call YieldColorOnlyGetsDarker();
  if (White(colorLocal)) {
       call MidWriteBarrier(tid);
  }

  yield;
}

procedure {:yields} {:phase 1,2} MidWriteBarrier({:linear "tid"} tid:Tid)
ensures {:atomic} |{ A: assert tid != nil;
                        goto B, C; 
                     B: assume White(Color);
                        Color := GRAY();
                        return true; 
                     C: return true;}|;
{
       var colorLocal:int;

       yield;
       call AcquireLock(tid);
       call colorLocal := GetColorLocked(tid);
       if (White(colorLocal)) {
           call SetColorLocked(tid, GRAY());
       } 
       call ReleaseLock(tid);
       yield;
}