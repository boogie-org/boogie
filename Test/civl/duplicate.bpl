type{:datatype} Addr;
function{:constructor} Some(i: int): Addr;
function{:constructor} None(): Addr;

function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;
function {:inline} {:linear "addr1"} IntCollector1(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}

function {:inline} {:linear "addr1"} AddrCollector1(x: Addr) : [int]bool
{
  if is#Some(x) then MapConstBool(false)[i#Some(x) := true] else MapConstBool(false)
}

function {:inline} {:linear "addr1"} IntsCollector1(xs: [int]bool) : [int]bool
{
  xs
}

function {:inline} {:linear "addr2"} IntCollector2(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}

function {:inline} {:linear "addr2"} IntsCollector2(xs: [int]bool) : [int]bool
{
  xs
}

var {:layer 0,3} {:linear} Addrs:[int]bool;  // ghost
var {:layer 0,3} done: [int]bool;
var {:layer 0,4} x:[int]int;

procedure {:yields} {:layer 0} {:refines "AtomicDoneUpdate"} DoneUpdate(i: int) returns ({:linear "addr1"} x: Addr);
procedure {:atomic} {:layer 1} AtomicDoneUpdate(i: int) returns ({:linear "addr1"} x: Addr)
modifies done, Addrs;
{
    if (done[i]) {
        x := None();
    } else {
        done[i] := true;
	Addrs[i] := false;
	x := Some(i);
    }
}

procedure {:yields} {:layer 0} {:refines "AtomicAddAddr"} AddAddr({:linear_in "addr1"} i1: int, {:linear "addr2"} i2: int);
procedure {:atomic} {:layer 3} AtomicAddAddr({:linear_in "addr1"} i1: int, {:linear "addr2"} i2: int)
modifies Addrs;
{
    assert i1 == i2;
    assert !done[i1];
    Addrs[i1] := true;
}

procedure {:yields} {:layer 0} {:refines "AtomicExtract"} Extract({:linear "addr1"} x: Addr) returns ({:linear "addr1"} i: int);
procedure {:both} {:layer 1} AtomicExtract({:linear "addr1"} x: Addr) returns ({:linear "addr1"} i: int)
{
    assert is#Some(x);
    i := i#Some(x);
}

procedure {:yields} {:layer 0} {:refines "AtomicIncrement"} Increment({:linear "addr1"} i: int);
procedure {:left} {:layer 1} AtomicIncrement({:linear "addr1"} i: int)
modifies x;
{
    x[i] := x[i] + 1;
}

procedure {:yields} {:layer 0} {:refines "AtomicMultiply"} Multiply({:linear "addr1"} i: int);
procedure {:left} {:layer 1} AtomicMultiply({:linear "addr1"} i: int)
modifies x;
{
    x[i] := 2*x[i];
}

procedure {:yields} {:layer 1} {:refines "AtomicRemoteIncrementBody"} RemoteIncrementBody(i: int)
{
    var {:linear "addr1"} j: int;
    var {:linear "addr1"} x: Addr;
    yield;
    call x := DoneUpdate(i);
    if (is#Some(x)) {
        call j := Extract(x);   
        call Increment(j);
	// linear j is available for making a async call to IncrementCallback
    }
    yield;
}
procedure {:atomic} {:layer 2} AtomicRemoteIncrementBody(i: int)
modifies done, x, Addrs;
{
    assert done[i] || Addrs[i];
    if (!done[i]) {
        done[i] := true;
	x[i] := x[i] + 1;
	Addrs[i] := false;
    }
}

procedure {:yields} {:layer 1} {:refines "AtomicRemoteMultiplyBody"} RemoteMultiplyBody(i: int)
{
    var {:linear "addr1"} j: int;
    var {:linear "addr1"} x: Addr;
    yield;
    call x := DoneUpdate(i);
    if (is#Some(x)) {
        call j := Extract(x);   
        call Multiply(j);
    }
    yield;
}
procedure {:atomic} {:layer 2} AtomicRemoteMultiplyBody(i: int)
modifies done, x, Addrs;
{
    assert done[i] || Addrs[i];
    if (!done[i]) {
        done[i] := true;
	x[i] := 2*x[i];
	Addrs[i] := false;
    }
}

type Op;
const unique INCREMENT: Op;
const unique MULTIPLY: Op;

procedure {:yields} {:layer 2} DuplicateRemote(i: int, op: Op)
requires {:layer 2} done[i];
{
    yield;
    assert {:layer 2} done[i];
    if (op == INCREMENT) {
        call RemoteIncrementBody(i);
    } else if (op == MULTIPLY) {
        call RemoteMultiplyBody(i);
    }
    yield;
}

procedure {:yields} {:layer 2} {:refines "AtomicRemoteIncrement"} RemoteIncrement(i1: int, {:linear_in "addr2"} i2: int)
{
    yield;
    call RemoteIncrementBody(i1);
    while (*)
    invariant {:terminates} {:layer 0,1,2} true;
    {
        async call DuplicateRemote(i1, INCREMENT);
    }
    yield;
}
procedure {:left} {:layer 3} AtomicRemoteIncrement(i1: int, {:linear_in "addr2"} i2: int)
modifies done, x, Addrs;
{
    assert i1 == i2;
    assert !done[i1] && Addrs[i1];
    done[i1] := true;
    x[i1] := x[i1] + 1;
    Addrs[i1] := false;
}

procedure {:yields} {:layer 2} {:refines "AtomicRemoteMultiply"} RemoteMultiply(i1: int, {:linear_in "addr2"} i2: int)
{
    yield;
    call RemoteMultiplyBody(i1);
    while (*)
    invariant {:terminates} {:layer 0,1,2} true;
    {
        async call DuplicateRemote(i1, MULTIPLY);
    }
    yield;
}
procedure {:left} {:layer 3} AtomicRemoteMultiply(i1: int, {:linear_in "addr2"} i2: int)
modifies done, x, Addrs;
{
    assert i1 == i2;
    assert !done[i1] && Addrs[i1];
    done[i1] := true;
    x[i1] := 2*x[i1];
    Addrs[i1] := false;
}

procedure {:yields} {:layer 3} {:refines "AtomicLocalIncrement"} LocalIncrement({:linear_in "addr1"} i1: int, {:linear_in "addr2"} i2: int)
requires {:layer 3} !done[i1];
{
    yield;
    assert {:layer 3} !done[i1];    
    call AddAddr(i1, i2);
    async call RemoteIncrement(i1, i2);
    yield;
}
procedure {:atomic} {:layer 4} AtomicLocalIncrement({:linear_in "addr1"} i1: int, {:linear_in "addr2"} i2: int)
modifies x;
{
    assert i1 == i2;
    x[i1] := x[i1] + 1;
}

procedure {:yields} {:layer 3} {:refines "AtomicLocalMultiply"} LocalMultiply({:linear_in "addr1"} i1: int, {:linear_in "addr2"} i2: int)
requires {:layer 3} !done[i1];
{
    yield;
    assert {:layer 3} !done[i1];    
    call AddAddr(i1, i2);
    async call RemoteMultiply(i1, i2);
    yield;
}
procedure {:atomic} {:layer 4} AtomicLocalMultiply({:linear_in "addr1"} i1: int, {:linear_in "addr2"} i2: int)
modifies x;
{
    assert i1 == i2;
    x[i1] := 2*x[i1];
}