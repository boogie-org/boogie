function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;
function {:inline} {:linear "addr"} AddrCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}

function {:inline} {:linear "addr"} AddrsCollector(xs: [int]bool) : [int]bool
{
  xs
}

var {:layer 0,1} done: [int]bool;
var {:layer 0,1} x:[int]int;
var {:layer 0,1} {:linear} Addrs:[int]bool;

procedure {:yields} {:layer 0} {:refines "AtomicDoneUpdate"} DoneUpdate(i: int) returns (status: bool);
procedure {:atomic} {:layer 1} AtomicDoneUpdate(i: int) returns (status: bool)
modifies done;
{
    status := !done[i];
    if (status) {
        done[i] := true;
    }
}

procedure {:yields} {:layer 0} {:refines "AtomicIncrement"} Increment({:linear "addr"} i: int);
procedure {:left} {:layer 1} AtomicIncrement({:linear "addr"} i: int)
modifies x;
{
    x[i] := x[i] + 1;
}

procedure {:yields} {:layer 0} {:refines "AtomicMultiply"} Multiply({:linear "addr"} i: int);
procedure {:left} {:layer 1} AtomicMultiply({:linear "addr"} i: int)
modifies x;
{
    x[i] := 2*x[i];
}

procedure {:yields} {:layer 0} {:refines "AtomicAddAddr"} AddAddr({:linear_in "addr"} i: int);
procedure {:atomic} {:layer 1} AtomicAddAddr({:linear_in "addr"} i: int)
modifies Addrs;
{
    Addrs[i] := true;
}

procedure {:yields} {:layer 0} {:refines "AtomicRemoveAddr"} RemoveAddr({:linear_out "addr"} i: int);
procedure {:left} {:layer 1} AtomicRemoveAddr({:linear_out "addr"} i: int)
modifies Addrs;
{
    assert Addrs[i];
    Addrs[i] := false;
}
