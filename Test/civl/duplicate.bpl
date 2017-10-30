function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;

type{:datatype} Addr;
function{:constructor} Addr(i:int, left:bool, right:bool):Addr;
function {:inline} {:linear "addr"} AddrCollector(x: Addr) : [int]bool
{
    MapConstBool(false)[-i#Addr(x) := left#Addr(x)][i#Addr(x) := right#Addr(x)]
}
function {:inline} {:linear "addr"} AddrSetCollector(x: [int]bool) : [int]bool
{
    x
}

function {:inline} isAddrWhole(i: int, l: Addr) : bool { i > 0 && l == Addr(i, true, true) }
function {:inline} isAddrLeft(i: int, l: Addr) : bool { i > 0 && l == Addr(i, true, false) }
function {:inline} isAddrRight(i: int, l: Addr) : bool { i > 0 && l == Addr(i, false, true) }

var {:layer 0,3} {:linear "addr"} Addrs:[int]bool;  // ghost
var {:layer 0,3} done: [int]int;
var {:layer 0,4} x:[int]int;

procedure {:yields} {:layer 0} {:refines "AtomicDoneUpdate"} DoneUpdate(i: int, {:linear_in "addr"} l: Addr, phase: int) returns ({:linear "addr"} l': Addr, b: bool);
procedure {:atomic} {:layer 1} AtomicDoneUpdate(i: int,  {:linear_in "addr"} l: Addr, phase: int) returns ({:linear "addr"} l': Addr, b: bool)
modifies done, Addrs;
{
    assert done[i] >= phase || (Addrs[i] && isAddrLeft(i, l));
    if (done[i] >= phase) {
        l' := l;
        b := false;
    } else {
        done[i] := phase;
        Addrs[i] := false;
        l' := Addr(i, true, true);
        b := true;
    }
}

procedure {:yields} {:layer 0} {:refines "AtomicAddAddr"} AddAddr(i: int, {:linear_in "addr"} l: Addr, phase: int) returns ({:linear "addr"} l': Addr);
procedure {:atomic} {:layer 1,3} AtomicAddAddr(i: int, {:linear_in "addr"} l: Addr, phase: int) returns ({:linear "addr"} l': Addr)
modifies Addrs;
{
    assert done[i] < phase && isAddrWhole(i, l);
    Addrs[i] := true;
    l' := Addr(i, true, false);
}

procedure {:yields} {:layer 0} {:refines "AtomicEmptyAddr"} EmptyAddr(i: int) returns ({:linear "addr"} l': Addr);
procedure {:both} {:layer 1,3} AtomicEmptyAddr(i: int) returns ({:linear "addr"} l': Addr)
{
    l' := Addr(i, false, false);
}

procedure {:yields} {:layer 0} {:refines "AtomicIncrement"} Increment(i: int, {:linear "addr"} l: Addr);
procedure {:left} {:layer 1} AtomicIncrement(i: int, {:linear "addr"} l: Addr)
modifies x;
{
    assert isAddrWhole(i, l);
    x[i] := x[i] + 1;
}

procedure {:yields} {:layer 0} {:refines "AtomicMultiply"} Multiply(i: int, {:linear "addr"} l: Addr);
procedure {:left} {:layer 1} AtomicMultiply(i: int, {:linear "addr"} l: Addr)
modifies x;
{
    assert isAddrWhole(i, l);
    x[i] := 2*x[i];
}

procedure {:yields} {:layer 1} {:refines "AtomicRemoteIncrementBody"} RemoteIncrementBody(i: int, {:linear_in "addr"} l: Addr, phase: int)
{
    var {:linear "addr"} l': Addr;
    var b: bool;
    yield;
    call l', b := DoneUpdate(i, l, phase);
    if (b) {
        call Increment(i, l');
        // linear l' is available for making a async call to IncrementCallback
    }
    yield;
}
procedure {:atomic} {:layer 2} AtomicRemoteIncrementBody(i: int, {:linear_in "addr"} l: Addr, phase: int)
modifies done, x, Addrs;
{
    assert done[i] >= phase || (Addrs[i] && isAddrLeft(i, l));
    if (done[i] < phase) {
        done[i] := phase;
        x[i] := x[i] + 1;
        Addrs[i] := false;
    }
}

procedure {:yields} {:layer 1} {:refines "AtomicRemoteMultiplyBody"} RemoteMultiplyBody(i: int, {:linear_in "addr"} l: Addr, phase: int)
{
    var {:linear "addr"} l': Addr;
    var b: bool;
    yield;
    call l', b := DoneUpdate(i, l, phase);
    if (b) {
        call Multiply(i, l');
        // linear l' is available for making a async call to MultiplyCallback
    }
    yield;
}
procedure {:atomic} {:layer 2} AtomicRemoteMultiplyBody(i: int, {:linear_in "addr"} l: Addr, phase: int)
modifies done, x, Addrs;
{
    assert done[i] >= phase || (Addrs[i] && isAddrLeft(i, l));
    if (done[i] < phase) {
        done[i] := phase;
        x[i] := 2*x[i];
        Addrs[i] := false;
    }
}

type Op;
const unique INCREMENT: Op;
const unique MULTIPLY: Op;

procedure {:yields} {:layer 2} DuplicateRemote(i: int, op: Op, phase: int)
requires {:layer 2} done[i] >= phase;
{
    var {:linear "addr"} l: Addr;
    yield;
    assert {:layer 2} done[i] >= phase;
    call l := EmptyAddr(i);
    if (op == INCREMENT) {
        call RemoteIncrementBody(i, l, phase);
    } else if (op == MULTIPLY) {
        call RemoteMultiplyBody(i, l, phase);
    }
    yield;
}

procedure {:yields} {:layer 2} {:refines "AtomicRemoteIncrement"} RemoteIncrement(i: int, {:linear_in "addr"} l: Addr, phase: int)
{
    yield;
    call RemoteIncrementBody(i, l, phase);
    while (*)
    invariant {:terminates} {:layer 0,1,2} true;
    {
        async call DuplicateRemote(i, INCREMENT, phase);
    }
    yield;
}
procedure {:left} {:layer 3} AtomicRemoteIncrement(i: int, {:linear_in "addr"} l: Addr, phase: int)
modifies done, x, Addrs;
{
    assert done[i] < phase && Addrs[i] && isAddrLeft(i, l);
    done[i] := phase;
    x[i] := x[i] + 1;
    Addrs[i] := false;
}

procedure {:yields} {:layer 2} {:refines "AtomicRemoteMultiply"} RemoteMultiply(i: int, {:linear_in "addr"} l: Addr, phase: int)
{
    yield;
    call RemoteMultiplyBody(i, l, phase);
    while (*)
    invariant {:terminates} {:layer 0,1,2} true;
    {
        async call DuplicateRemote(i, MULTIPLY, phase);
    }
    yield;
}
procedure {:left} {:layer 3} AtomicRemoteMultiply(i: int, {:linear_in "addr"} l: Addr, phase: int)
modifies done, x, Addrs;
{
    assert done[i] < phase && Addrs[i] && isAddrLeft(i, l);
    done[i] := phase;
    x[i] := 2*x[i];
    Addrs[i] := false;
}

procedure {:yields} {:layer 3} {:refines "AtomicLocalIncrement"} LocalIncrement(i: int, {:linear_in "addr"} l: Addr, phase: int)
requires {:layer 3} done[i] < phase && isAddrWhole(i, l);
{
    var {:linear "addr"} l': Addr;
    yield;
    assert {:layer 3} done[i] < phase && isAddrWhole(i, l);
    call l' := AddAddr(i, l, phase);
    async call RemoteIncrement(i, l', phase);
    yield;
}
procedure {:atomic} {:layer 4} AtomicLocalIncrement(i: int, {:linear_in "addr"} l: Addr, phase: int)
modifies x;
{
    assert isAddrWhole(i, l);
    x[i] := x[i] + 1;
}

procedure {:yields} {:layer 3} {:refines "AtomicLocalMultiply"} LocalMultiply(i: int, {:linear_in "addr"} l: Addr, phase: int)
requires {:layer 3} done[i] < phase && isAddrWhole(i, l);
{
    var {:linear "addr"} l': Addr;
    yield;
    assert {:layer 3} done[i] < phase && isAddrWhole(i, l);
    call l' := AddAddr(i, l, phase);
    async call RemoteMultiply(i, l', phase);
    yield;
}
procedure {:atomic} {:layer 4} AtomicLocalMultiply(i: int, {:linear_in "addr"} l: Addr, phase: int)
modifies x;
{
    assert isAddrWhole(i, l);
    x[i] := 2*x[i];
}
