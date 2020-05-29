// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x: int;

procedure {:yield_invariant} {:layer 1} Yield();

procedure {:yields} {:layer 1} {:refines "atomic_incr_by_two"} incr_by_two_bad()
{
    yield;
    par incr() | incr() | Yield() | incr();
    call incr();
    yield;
}

procedure {:yields} {:layer 1} {:refines "atomic_incr_by_two"} incr_by_two()
{
    yield;
    par incr() | decr() | Yield() | incr();
    call incr();
    yield;
}
procedure {:both} {:layer 1,2} atomic_incr_by_two()
modifies x;
{
    x := x + 2;
}

procedure {:both} {:layer 1,1} atomic_incr()
modifies x;
{
    x := x + 1;
}
procedure {:yields} {:layer 0} {:refines "atomic_incr"} incr();

procedure {:both} {:layer 1,1} atomic_decr()
modifies x;
{
    x := x - 1;
}
procedure {:yields} {:layer 0} {:refines "atomic_decr"} decr();
