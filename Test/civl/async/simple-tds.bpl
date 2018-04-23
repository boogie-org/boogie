// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "MapConst"} MapConstBool(bool): [int]bool;
function {:inline} {:linear "tid"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}

var {:layer 0,5} x: int;
const unique p: int;
const unique q: int;
const unique r: int;

procedure {:yields} {:layer 0} {:refines "AtomicP0"} P0({:linear "tid"} tid: int);
procedure {:left} {:layer 1} AtomicP0({:linear "tid"} tid: int)
modifies x;
{ assert tid == p; assert x == 0; x := 1; }

procedure {:yields} {:layer 0} {:refines "AtomicQ0"} Q0({:linear "tid"} tid: int);
procedure {:atomic} {:layer 1} AtomicQ0({:linear "tid"} tid: int)
modifies x;
{ assert tid == q; assume x == 1; x := 2; }

procedure {:yields} {:layer 0} {:refines "AtomicR0"} R0({:linear "tid"} tid: int);
procedure {:atomic} {:layer 1,3} AtomicR0({:linear "tid"} tid: int)
modifies x;
{ assert tid == r; assume x == 2; x := 3; }

procedure {:yields} {:layer 1} {:refines "AtomicP1"} P1({:linear_in "tid"} tid: int) { yield; async call P0(tid); yield; }
procedure {:atomic} {:layer 2,3} AtomicP1({:linear_in "tid"} tid: int)
modifies x;
{ assert tid == p; assert x == 0; x := 1; }

procedure {:yields} {:layer 1} {:refines "AtomicQ1"} Q1({:linear "tid"} tid: int) { yield; call Q0(tid); yield; }
procedure {:left} {:layer 2,3} AtomicQ1({:linear "tid"} tid: int)
modifies x;
{ assert tid == q; assert x == 1; x := 2; }

procedure {:yields} {:layer 3} {:refines "AtomicR3"} R3({:linear "tid"} tid: int) { yield; call R0(tid); yield; }
procedure {:left} {:layer 4} AtomicR3({:linear "tid"} tid: int)
modifies x;
{ assert tid == r; assert x == 2; x := 3; }

procedure {:yields} {:layer 3} {:refines "AtomicMain3"} Main3({:linear_in "tid"} tidp: int, {:linear_in "tid"} tidq: int) {
    yield;
    call P1(tidp);
    async call Q1(tidq);
    yield;
}
procedure {:atomic} {:layer 4} AtomicMain3({:linear_in "tid"} tidp: int, {:linear_in "tid"} tidq: int)
modifies x;
{ assert tidp == p && tidq == q; assert x == 0; x := 2; }

procedure {:yields} {:layer 4} {:refines "AtomicMain4"} Main4({:linear_in "tid"} tidp: int, {:linear_in "tid"} tidq: int, {:linear_in "tid"} tidr: int) {
    yield;
    call Main3(tidp, tidq);
    async call R3(tidr);
    yield;
}
procedure {:atomic} {:layer 5} AtomicMain4({:linear_in "tid"} tidp: int, {:linear_in "tid"} tidq: int, {:linear_in "tid"} tidr: int)
modifies x;
{ assert tidp == p && tidq == q && tidr == r; assert x == 0; x := 3; }
