// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type Tid; 
function {:builtin "MapConst"} MapConstBool(bool): [Tid]bool;
function {:builtin "MapOr"} MapOr([Tid]bool, [Tid]bool) : [Tid]bool;

function {:inline} {:linear "tid"} TidCollector(x: Tid) : [Tid]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [Tid]bool) : [Tid]bool
{
  x
}

var {:linear "tid"} {:phase 1} alloc:[Tid]bool; 
var {:phase 1} a:[Tid]int;

procedure Allocate() returns ({:linear "tid"} tid:Tid); 
modifies alloc; 

procedure {:yields} {:phase 1} main() { 
    var {:linear "tid"} tid:Tid;

    yield;
    while (true) { 
        call tid := Allocate(); 
	async call P(tid); 
	yield;
    }
    yield;
}

procedure {:yields} {:phase 1} P({:linear "tid"} tid: Tid) 
ensures {:phase 1} a[tid] == old(a)[tid] + 1; 
{ 
    var t:int;

    yield;
    assert {:phase 1} a[tid] == old(a)[tid];
    call t := Read(tid); 
    yield;
    assert {:phase 1} a[tid] == t; 
    call Write(tid, t + 1); 
    yield;
    assert {:phase 1} a[tid] == t + 1; 
}

procedure {:yields} {:phase 0,1} Read({:linear "tid"} tid: Tid) returns (val: int);
ensures {:atomic}
|{A:
  val := a[tid]; return true;
}|;

procedure {:yields} {:phase 0,1} Write({:linear "tid"} tid: Tid, val: int);
ensures {:atomic}
|{A:
  a[tid] := val; return true;
}|;
