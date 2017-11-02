// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} {:linear "addr"} Addrs:[int]bool;

// This test exposed an unsoundness due to linearity assumes. In particular, the
// linear_out parameter of RemoveAddr was still part of the disjointness
// expression in the post-state.

procedure {:atomic} {:layer 1,2} AddAddr({:linear_in "addr"} i: int)
modifies Addrs;
{
    Addrs[i] := true;
}

// Gate not preserved by itself
procedure {:left} {:layer 1} RemoveAddr_1({:linear_out "addr"} i: int)
modifies Addrs;
{
    assert Addrs[i];
    Addrs[i] := false;
}

// Without the gate, RemoveAddr does not commute with AddAddr
procedure {:left} {:layer 2} RemoveAddr_2({:linear_out "addr"} i: int)
modifies Addrs;
{
    Addrs[i] := false;
}

////////////////////////////////////////////////////////////////////////////////

function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;
function {:inline} {:linear "addr"} AddrCollector(x: int) : [int]bool
{ MapConstBool(false)[x := true] }
function {:inline} {:linear "addr"} AddrsCollector(xs: [int]bool) : [int]bool
{ xs }
