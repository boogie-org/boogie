// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X;
const nil: X;
function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [X]bool) : [X]bool
{
  x
}

var {:layer 0,3} A: X;
var {:layer 0,3} B: X;
var {:layer 0,3} counter: int;
var {:layer 0,3}{:linear "tid"} unallocated:[X]bool;

procedure {:right} {:layer 1,3} AtomicLockA({:linear "tid"} tid: X)
modifies A;
{ assert tid != nil; assume A == nil; A := tid; }

procedure {:yields} {:layer 0} {:refines "AtomicLockA"} LockA({:linear "tid"} tid: X);

procedure {:right} {:layer 1} AtomicIncrA({:linear "tid"} tid: X)
modifies counter;
{ assert tid != nil && A == tid; counter := counter + 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncrA"} IncrA({:linear "tid"} tid: X);

procedure {:right} {:layer 1} AtomicDecrA({:linear "tid"} tid: X)
modifies counter;
{ assert tid != nil && A == tid; counter := counter - 1; }

procedure {:yields} {:layer 0} {:refines "AtomicDecrA"} DecrA({:linear "tid"} tid: X);

procedure {:left} {:layer 1,3} AtomicUnlockA({:linear "tid"} tid: X)
modifies A;
{ assert tid != nil && A == tid; A := nil; }

procedure {:yields} {:layer 0} {:refines "AtomicUnlockA"} UnlockA({:linear "tid"} tid: X);

procedure {:right} {:layer 1,3} AtomicLockB({:linear "tid"} tid: X)
modifies B;
{ assert tid != nil; assume B == nil; B := tid; }

procedure {:yields} {:layer 0} {:refines "AtomicLockB"} LockB({:linear "tid"} tid: X);

procedure {:atomic} {:layer 1,2} AtomicIncrB({:linear "tid"} tid: X)
modifies counter;
{ assert tid != nil && B == tid; counter := counter + 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncrB"} IncrB({:linear "tid"} tid: X);

procedure {:atomic} {:layer 1} AtomicDecrB({:linear "tid"} tid: X)
modifies counter;
{ assert tid != nil && B == tid; counter := counter - 1; }

procedure {:yields} {:layer 0} {:refines "AtomicDecrB"} DecrB({:linear "tid"} tid: X);

procedure {:left} {:layer 1,3} AtomicUnlockB({:linear "tid"} tid: X)
modifies B;
{ assert tid != nil && B == tid; B := nil; }

procedure {:yields} {:layer 0} {:refines "AtomicUnlockB"} UnlockB({:linear "tid"} tid: X);

procedure {:atomic} {:layer 1,3} AtomicAssertA({:linear "tid"} tid: X)
{ assert tid != nil && A == tid; assert counter >= -1; }

procedure {:yields} {:layer 0} {:refines "AtomicAssertA"} AssertA({:linear "tid"} tid: X);

procedure {:atomic} {:layer 1,3} AtomicAssertB({:linear "tid"} tid: X)
{ assert tid != nil && A == tid && B == tid; assert counter == 0; }

procedure {:yields} {:layer 0} {:refines "AtomicAssertB"} AssertB({:linear "tid"} tid: X);

procedure {:right} {:layer 1,3} AtomicAllocTid() returns ({:linear "tid"} tid: X)
modifies unallocated;
{
  assume tid != nil;
  assume unallocated[tid];
  unallocated[tid] := false;
}

procedure {:yields} {:layer 0} {:refines "AtomicAllocTid"} AllocTid() returns ({:linear "tid"} tid: X);

procedure {:right} {:layer 2} AtomicAbsDecrB({:linear "tid"} tid: X)
modifies counter;
{ assert tid != nil && B == tid && counter == 0; counter := counter - 1; }

procedure {:yields} {:layer 1} {:refines "AtomicAbsDecrB"} AbsDecrB({:linear "tid"} tid: X)
{
    yield;
    call DecrB(tid);
    yield;
}

procedure {:both} {:layer 3} AtomicAbsAssertA({:linear "tid"} tid: X)
{ assert tid != nil && A == tid; assert counter >= -1; }

procedure {:yields} {:layer 2} {:refines "AtomicAbsAssertA"} AbsAssertA({:linear "tid"} tid: X)
{
    yield;
    call AssertA(tid);
    yield;
}

procedure {:both} {:layer 3} AtomicAbsAssertB({:linear "tid"} tid: X)
{ assert tid != nil && A == tid && B == tid; assert counter == 0; }

procedure {:yields} {:layer 2} {:refines "AtomicAbsAssertB"} AbsAssertB({:linear "tid"} tid: X)
{
    yield;
    call AssertB(tid);
    yield;
}

procedure {:yields} {:layer 1} TA({:linear "tid"} tid: X)
requires {:layer 1} tid != nil;
{
    yield;
    call LockA(tid);
    call IncrA(tid);
    call DecrA(tid);
    call UnlockA(tid);
    yield;
}

procedure {:both} {:layer 3} AtomicTB({:linear "tid"} tid: X)
{ assert tid != nil && counter == 0; }

procedure {:yields} {:layer 2} {:refines "AtomicTB"} TB({:linear "tid"} tid: X)
{
    yield;
    call LockB(tid);
    call AbsDecrB(tid);
    call IncrB(tid);
    call UnlockB(tid);
    yield;
}

procedure {:yields} {:layer 3} AbsTB({:linear "tid"} tid: X)
requires {:layer 3} tid != nil && counter == 0;
{
    yield;
    assert {:layer 3} counter == 0;
    call TB(tid);
    yield;
}

procedure {:yields} {:layer 3} main({:linear "tid"} tid: X)
requires {:layer 3} tid != nil && counter == 0;
{
    var {:linear "tid"} cid: X;
    
    yield;
    assert {:layer 3} counter == 0;
    while (*)
    invariant {:layer 3} counter == 0;
    {
        if (*) {
            call cid := AllocTid();
            async call TA(cid);
        }
        yield;
        assert {:layer 3} counter == 0;
        if (*) {
            call cid := AllocTid();
            async call AbsTB(cid);
        }
        yield;
        assert {:layer 3} counter == 0;
        call LockA(tid);
        call AbsAssertA(tid);
        call LockB(tid);
        call AbsAssertB(tid);
        call UnlockB(tid);
        call UnlockA(tid);
        yield;
        assert {:layer 3} counter == 0;
    }
    yield;
}
