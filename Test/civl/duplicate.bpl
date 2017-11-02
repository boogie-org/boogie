// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// XFAIL: *

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

const IncrementPhase: int;
const MultiplyPhase: int;
axiom 1 < IncrementPhase;
axiom IncrementPhase + 1 < MultiplyPhase;

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

procedure {:yields} {:layer 1} {:refines "AtomicRemoteIncrementBody"} RemoteIncrementBody(i: int, {:linear_in "addr"} l: Addr)
{
    var {:linear "addr"} l': Addr;
    var b: bool;
    yield;
    call l', b := DoneUpdate(i, l, IncrementPhase);
    if (b) {
        call Increment(i, l');
        // linear l' is available for making a async call to IncrementCallback
    }
    yield;
}
procedure {:atomic} {:layer 2} AtomicRemoteIncrementBody(i: int, {:linear_in "addr"} l: Addr)
modifies done, x, Addrs;
{
    assert done[i] >= IncrementPhase || (Addrs[i] && isAddrLeft(i, l));
    if (done[i] < IncrementPhase) {
        done[i] := IncrementPhase;
	x[i] := x[i] + 1;
	Addrs[i] := false;
    }
}

procedure {:yields} {:layer 1} {:refines "AtomicRemoteMultiplyBody"} RemoteMultiplyBody(i: int, {:linear_in "addr"} l: Addr)
{
    var {:linear "addr"} l': Addr;
    var b: bool;
    yield;
    call l', b := DoneUpdate(i, l, MultiplyPhase);
    if (b) {
        call Multiply(i, l');
        // linear l' is available for making a async call to MultiplyCallback
    }
    yield;
}
procedure {:atomic} {:layer 2} AtomicRemoteMultiplyBody(i: int, {:linear_in "addr"} l: Addr)
modifies done, x, Addrs;
{
    assert done[i] >= MultiplyPhase || (Addrs[i] && isAddrLeft(i, l));
    if (done[i] < MultiplyPhase) {
        done[i] := MultiplyPhase;
	x[i] := 2*x[i];
	Addrs[i] := false;
    }
}

type Op;
const unique INCREMENT: Op;
const unique MULTIPLY: Op;

procedure {:yields} {:layer 2} DuplicateIncrementRemote(i: int)
requires {:layer 2} done[i] >= IncrementPhase;
{
    var {:linear "addr"} l: Addr;
    yield;
    assert {:layer 2} done[i] >= IncrementPhase;
    call l := EmptyAddr(i);
    call RemoteIncrementBody(i, l);
    yield;
}

procedure {:yields} {:layer 2} DuplicateMultiplyRemote(i: int)
requires {:layer 2} done[i] >= MultiplyPhase;
{
    var {:linear "addr"} l: Addr;
    yield;
    assert {:layer 2} done[i] >= MultiplyPhase;
    call l := EmptyAddr(i);
    call RemoteMultiplyBody(i, l);
    yield;
}

procedure {:yields} {:layer 2} {:refines "AtomicRemoteIncrement"} RemoteIncrement(i: int, {:linear_in "addr"} l: Addr)
{
    yield;
    call RemoteIncrementBody(i, l);
    while (*)
    invariant {:terminates} {:layer 0,1,2} true;
    {
        async call DuplicateIncrementRemote(i);
    }
    yield;
}
procedure {:left} {:layer 3} AtomicRemoteIncrement(i: int, {:linear_in "addr"} l: Addr)
modifies done, x, Addrs;
{
    assert done[i] < IncrementPhase && Addrs[i] && isAddrLeft(i, l);
    done[i] := IncrementPhase;
    x[i] := x[i] + 1;
    Addrs[i] := false;
}

procedure {:yields} {:layer 2} {:refines "AtomicRemoteMultiply"} RemoteMultiply(i: int, {:linear_in "addr"} l: Addr)
{
    yield;
    call RemoteMultiplyBody(i, l);
    while (*)
    invariant {:terminates} {:layer 0,1,2} true;
    {
        async call DuplicateMultiplyRemote(i);
    }
    yield;
}
procedure {:left} {:layer 3} AtomicRemoteMultiply(i: int, {:linear_in "addr"} l: Addr)
modifies done, x, Addrs;
{
    assert done[i] < MultiplyPhase && Addrs[i] && isAddrLeft(i, l);
    done[i] :=  MultiplyPhase;
    x[i] := 2*x[i];
    Addrs[i] := false;
}

procedure {:yields} {:layer 3} {:refines "AtomicLocalIncrement"} LocalIncrement(i: int, {:linear_in "addr"} l: Addr)
requires {:layer 3} done[i] < IncrementPhase && isAddrWhole(i, l);
{
    var {:linear "addr"} l': Addr;
    yield;
    assert {:layer 3} done[i] < IncrementPhase && isAddrWhole(i, l);
    call l' := AddAddr(i, l, IncrementPhase);
    async call RemoteIncrement(i, l');
    yield;
}
procedure {:atomic} {:layer 4} AtomicLocalIncrement(i: int, {:linear_in "addr"} l: Addr)
modifies x;
{
    assert isAddrWhole(i, l);
    x[i] := x[i] + 1;
}

procedure {:yields} {:layer 3} {:refines "AtomicLocalMultiply"} LocalMultiply(i: int, {:linear_in "addr"} l: Addr)
requires {:layer 3} done[i] < MultiplyPhase && isAddrWhole(i, l);
{
    var {:linear "addr"} l': Addr;
    yield;
    assert {:layer 3} done[i] < MultiplyPhase && isAddrWhole(i, l);
    call l' := AddAddr(i, l, MultiplyPhase);
    async call RemoteMultiply(i, l');
    yield;
}
procedure {:atomic} {:layer 4} AtomicLocalMultiply(i: int, {:linear_in "addr"} l: Addr)
modifies x;
{
    assert isAddrWhole(i, l);
    x[i] := 2*x[i];
}
