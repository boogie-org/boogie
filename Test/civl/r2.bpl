// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x: int;

procedure {:yields} {:layer 1} {:refines "atomic_incr"} foo1() {
    par {:refines} incr() | nop() | nop();
}

procedure {:yields} {:layer 1} {:refines "atomic_incr"} foo2() {
    par incr() | {:refines} nop() | nop();
}

procedure {:atomic} {:layer 1,2} atomic_incr()
modifies x;
{
    x := x + 1;
}
procedure {:yields} {:layer 1} {:refines "atomic_incr"} incr();

procedure {:atomic} {:layer 1,2} atomic_nop()
{
}
procedure {:yields} {:layer 1} {:refines "atomic_nop"} nop();
