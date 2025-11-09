// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type X;
const nil: X;

var {:layer 0,3} A: X;
var {:layer 0,3} B: X;
var {:layer 0,3} counter: int;
var {:layer 0,3}{:linear} unallocated: Set X;

right action {:layer 1,3} AtomicLockA({:linear} tid: One X)
modifies A;
{ assert tid->val != nil; assume A == nil; A := tid->val; }

yield procedure {:layer 0} LockA({:linear} tid: One X);
refines AtomicLockA;

right action {:layer 1} AtomicIncrA({:linear} tid: One X)
modifies counter;
{ assert tid->val != nil && A == tid->val; counter := counter + 1; }

yield procedure {:layer 0} IncrA({:linear} tid: One X);
refines AtomicIncrA;

right action {:layer 1} AtomicDecrA({:linear} tid: One X)
modifies counter;
{ assert tid->val != nil && A == tid->val; counter := counter - 1; }

yield procedure {:layer 0} DecrA({:linear} tid: One X);
refines AtomicDecrA;

left action {:layer 1,3} AtomicUnlockA({:linear} tid: One X)
modifies A;
{ assert tid->val != nil && A == tid->val; A := nil; }

yield procedure {:layer 0} UnlockA({:linear} tid: One X);
refines AtomicUnlockA;

right action {:layer 1,3} AtomicLockB({:linear} tid: One X)
modifies B;
{ assert tid->val != nil; assume B == nil; B := tid->val; }

yield procedure {:layer 0} LockB({:linear} tid: One X);
refines AtomicLockB;

atomic action {:layer 1,2} AtomicIncrB({:linear} tid: One X)
modifies counter;
{ assert tid->val != nil && B == tid->val; counter := counter + 1; }

yield procedure {:layer 0} IncrB({:linear} tid: One X);
refines AtomicIncrB;

atomic action {:layer 1} AtomicDecrB({:linear} tid: One X)
modifies counter;
{ assert tid->val != nil && B == tid->val; counter := counter - 1; }

yield procedure {:layer 0} DecrB({:linear} tid: One X);
refines AtomicDecrB;

left action {:layer 1,3} AtomicUnlockB({:linear} tid: One X)
modifies B;
{ assert tid->val != nil && B == tid->val; B := nil; }

yield procedure {:layer 0} UnlockB({:linear} tid: One X);
refines AtomicUnlockB;

atomic action {:layer 1,3} AtomicAssertA({:linear} tid: One X)
{ assert tid->val != nil && A == tid->val; assert counter >= -1; }

yield procedure {:layer 0} AssertA({:linear} tid: One X);
refines AtomicAssertA;

atomic action {:layer 1,3} AtomicAssertB({:linear} tid: One X)
{ assert tid->val != nil && A == tid->val && B == tid->val; assert counter == 0; }

yield procedure {:layer 0} AssertB({:linear} tid: One X);
refines AtomicAssertB;

right action {:layer 1,3} AtomicAllocTid() returns ({:linear} tid: One X)
modifies unallocated;
{
  var x: X;
  assume x != nil && Set_Contains(unallocated, x);
  call tid := One_Get(unallocated, x);
}

yield procedure {:layer 0} AllocTid() returns ({:linear} tid: One X);
refines AtomicAllocTid;

right action {:layer 2} AtomicAbsDecrB({:linear} tid: One X)
modifies counter;
{ assert tid->val != nil && B == tid->val && counter == 0; counter := counter - 1; }

yield procedure {:layer 1} AbsDecrB({:linear} tid: One X)
refines AtomicAbsDecrB;
{
    call DecrB(tid);
}

both action {:layer 3} AtomicAbsAssertA({:linear} tid: One X)
{ assert tid->val != nil && A == tid->val; assert counter >= -1; }

yield procedure {:layer 2} AbsAssertA({:linear} tid: One X)
refines AtomicAbsAssertA;
{
    call AssertA(tid);
}

both action {:layer 3} AtomicAbsAssertB({:linear} tid: One X)
{ assert tid->val != nil && A == tid->val && B == tid->val; assert counter == 0; }

yield procedure {:layer 2} AbsAssertB({:linear} tid: One X)
refines AtomicAbsAssertB;
{
    call AssertB(tid);
}

yield procedure {:layer 1} TA({:linear} tid: One X)
requires {:layer 1} tid->val != nil;
{
    call LockA(tid);
    call IncrA(tid);
    call DecrA(tid);
    call UnlockA(tid);
}

both action {:layer 3} AtomicTB({:linear} tid: One X)
{ assert tid->val != nil && counter == 0; }

yield procedure {:layer 2} TB({:linear} tid: One X)
refines AtomicTB;
{
    call LockB(tid);
    call AbsDecrB(tid);
    call IncrB(tid);
    call UnlockB(tid);
}

yield procedure {:layer 3} AbsTB({:linear} tid: One X)
requires {:layer 3} tid->val != nil;
requires call YieldCounter();
{
    call TB(tid);
}

yield procedure {:layer 3} main({:linear} tid: One X)
requires {:layer 3} tid->val != nil;
requires call YieldCounter();
{
    var {:linear} cid: One X;

    while (*)
    invariant {:yields} true;
    invariant call YieldCounter();
    {
        if (*) {
            call cid := AllocTid();
            async call TA(cid);
        }
        call Yield() | YieldCounter();
        if (*) {
            call cid := AllocTid();
            async call AbsTB(cid);
        }
        call Yield() | YieldCounter();
        call LockA(tid);
        call AbsAssertA(tid);
        call LockB(tid);
        call AbsAssertB(tid);
        call UnlockB(tid);
        call UnlockA(tid);
    }
}

yield procedure {:layer 2} Yield();

yield invariant {:layer 3} YieldCounter();
preserves counter == 0;
