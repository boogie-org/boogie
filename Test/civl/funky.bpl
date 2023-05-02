// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "tid"} X;
const nil: X;

var {:layer 0,3} A: X;
var {:layer 0,3} B: X;
var {:layer 0,3} counter: int;
var {:layer 0,3}{:linear "tid"} unallocated:[X]bool;

-> action {:layer 1,3} AtomicLockA({:linear "tid"} tid: X)
modifies A;
{ assert tid != nil; assume A == nil; A := tid; }

yield procedure {:layer 0} LockA({:linear "tid"} tid: X);
refines AtomicLockA;

-> action {:layer 1} AtomicIncrA({:linear "tid"} tid: X)
modifies counter;
{ assert tid != nil && A == tid; counter := counter + 1; }

yield procedure {:layer 0} IncrA({:linear "tid"} tid: X);
refines AtomicIncrA;

-> action {:layer 1} AtomicDecrA({:linear "tid"} tid: X)
modifies counter;
{ assert tid != nil && A == tid; counter := counter - 1; }

yield procedure {:layer 0} DecrA({:linear "tid"} tid: X);
refines AtomicDecrA;

<- action {:layer 1,3} AtomicUnlockA({:linear "tid"} tid: X)
modifies A;
{ assert tid != nil && A == tid; A := nil; }

yield procedure {:layer 0} UnlockA({:linear "tid"} tid: X);
refines AtomicUnlockA;

-> action {:layer 1,3} AtomicLockB({:linear "tid"} tid: X)
modifies B;
{ assert tid != nil; assume B == nil; B := tid; }

yield procedure {:layer 0} LockB({:linear "tid"} tid: X);
refines AtomicLockB;

>-< action {:layer 1,2} AtomicIncrB({:linear "tid"} tid: X)
modifies counter;
{ assert tid != nil && B == tid; counter := counter + 1; }

yield procedure {:layer 0} IncrB({:linear "tid"} tid: X);
refines AtomicIncrB;

>-< action {:layer 1} AtomicDecrB({:linear "tid"} tid: X)
modifies counter;
{ assert tid != nil && B == tid; counter := counter - 1; }

yield procedure {:layer 0} DecrB({:linear "tid"} tid: X);
refines AtomicDecrB;

<- action {:layer 1,3} AtomicUnlockB({:linear "tid"} tid: X)
modifies B;
{ assert tid != nil && B == tid; B := nil; }

yield procedure {:layer 0} UnlockB({:linear "tid"} tid: X);
refines AtomicUnlockB;

>-< action {:layer 1,3} AtomicAssertA({:linear "tid"} tid: X)
{ assert tid != nil && A == tid; assert counter >= -1; }

yield procedure {:layer 0} AssertA({:linear "tid"} tid: X);
refines AtomicAssertA;

>-< action {:layer 1,3} AtomicAssertB({:linear "tid"} tid: X)
{ assert tid != nil && A == tid && B == tid; assert counter == 0; }

yield procedure {:layer 0} AssertB({:linear "tid"} tid: X);
refines AtomicAssertB;

-> action {:layer 1,3} AtomicAllocTid() returns ({:linear "tid"} tid: X)
modifies unallocated;
{
  assume tid != nil;
  assume unallocated[tid];
  unallocated[tid] := false;
}

yield procedure {:layer 0} AllocTid() returns ({:linear "tid"} tid: X);
refines AtomicAllocTid;

-> action {:layer 2} AtomicAbsDecrB({:linear "tid"} tid: X)
modifies counter;
{ assert tid != nil && B == tid && counter == 0; counter := counter - 1; }

yield procedure {:layer 1} AbsDecrB({:linear "tid"} tid: X)
refines AtomicAbsDecrB;
{
    call DecrB(tid);
}

<-> action {:layer 3} AtomicAbsAssertA({:linear "tid"} tid: X)
{ assert tid != nil && A == tid; assert counter >= -1; }

yield procedure {:layer 2} AbsAssertA({:linear "tid"} tid: X)
refines AtomicAbsAssertA;
{
    call AssertA(tid);
}

<-> action {:layer 3} AtomicAbsAssertB({:linear "tid"} tid: X)
{ assert tid != nil && A == tid && B == tid; assert counter == 0; }

yield procedure {:layer 2} AbsAssertB({:linear "tid"} tid: X)
refines AtomicAbsAssertB;
{
    call AssertB(tid);
}

yield procedure {:layer 1} TA({:linear "tid"} tid: X)
requires {:layer 1} tid != nil;
{
    call LockA(tid);
    call IncrA(tid);
    call DecrA(tid);
    call UnlockA(tid);
}

<-> action {:layer 3} AtomicTB({:linear "tid"} tid: X)
{ assert tid != nil && counter == 0; }

yield procedure {:layer 2} TB({:linear "tid"} tid: X)
refines AtomicTB;
{
    call LockB(tid);
    call AbsDecrB(tid);
    call IncrB(tid);
    call UnlockB(tid);
}

yield procedure {:layer 3} AbsTB({:linear "tid"} tid: X)
requires {:layer 3} tid != nil;
requires call YieldCounter();
{
    call TB(tid);
}

yield procedure {:layer 3} main({:linear "tid"} tid: X)
requires {:layer 3} tid != nil;
requires call YieldCounter();
{
    var {:linear "tid"} cid: X;

    while (*)
    invariant {:yields} true;
    invariant call YieldCounter();
    {
        if (*) {
            call cid := AllocTid();
            async call TA(cid);
        }
        par Yield() | YieldCounter();
        if (*) {
            call cid := AllocTid();
            async call AbsTB(cid);
        }
        par Yield() | YieldCounter();
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
invariant counter == 0;
