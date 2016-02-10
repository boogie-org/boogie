// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X;
const nil: X;
function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}

var {:layer 0, 3} A: X;
var {:layer 0, 3} B: X;
var {:layer 0, 3} counter: int;

procedure {:yields} {:layer 0, 3} LockA({:linear "tid"} tid: X);
ensures {:right} |{ A: assert tid != nil; assume A == nil; A := tid; return true; }|;

procedure {:yields} {:layer 0, 1} IncrA({:linear "tid"} tid: X);
ensures {:right} |{ A: assert tid != nil && A == tid; counter := counter + 1; return true; }|;

procedure {:yields} {:layer 0, 1} DecrA({:linear "tid"} tid: X);
ensures {:right} |{ A: assert tid != nil && A == tid; counter := counter - 1; return true; }|;

procedure {:yields} {:layer 0, 3} UnlockA({:linear "tid"} tid: X);
ensures {:left} |{ A: assert tid != nil && A == tid; A := nil; return true; }|;

procedure {:yields} {:layer 0, 3} LockB({:linear "tid"} tid: X);
ensures {:right} |{ A: assert tid != nil; assume B == nil; B := tid; return true; }|;

procedure {:yields} {:layer 0, 2} IncrB({:linear "tid"} tid: X);
ensures {:atomic} |{ A: assert tid != nil && B == tid; counter := counter + 1; return true; }|;

procedure {:yields} {:layer 0, 1} DecrB({:linear "tid"} tid: X);
ensures {:atomic} |{ A: assert tid != nil && B == tid; counter := counter - 1; return true; }|;

procedure {:yields} {:layer 0, 3} UnlockB({:linear "tid"} tid: X);
ensures {:left} |{ A: assert tid != nil && B == tid; B := nil; return true; }|;

procedure {:yields} {:layer 0, 3} AssertA({:linear "tid"} tid: X);
ensures {:atomic} |{ A: assert tid != nil && A == tid; assert counter >= -1; return true; }|;

procedure {:yields} {:layer 0, 3} AssertB({:linear "tid"} tid: X);
ensures {:atomic} |{ A: assert tid != nil && A == tid && B == tid; assert counter == 0; return true; }|;

procedure {:pure} AllocTid() returns ({:linear "tid"} tid: X);
ensures tid != nil;

procedure {:yields} {:layer 1, 2} AbsDecrB({:linear "tid"} tid: X)
ensures {:right} |{ A: assert tid != nil && B == tid && counter == 0; counter := counter - 1; return true; }|;
{
    yield;
    call DecrB(tid);
    yield;
}

procedure {:yields} {:layer 2, 3} AbsAssertA({:linear "tid"} tid: X)
ensures {:both} |{ A: assert tid != nil && A == tid; assert counter >= -1; return true; }|;
{
    yield;
    call AssertA(tid);
    yield;
}

procedure {:yields} {:layer 2, 3} AbsAssertB({:linear "tid"} tid: X)
ensures {:both} |{ A: assert tid != nil && A == tid && B == tid; assert counter == 0; return true; }|;
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

procedure {:yields} {:layer 2, 3} TB({:linear "tid"} tid: X)
ensures {:both} |{ A: assert tid != nil && counter == 0; return true; }|;
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