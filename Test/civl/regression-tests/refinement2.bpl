// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: batch_mode

var {:layer 0,2} x: int;

yield procedure {:layer 1} foo1()
refines atomic_incr;
{
    call {:mark} incr() | nop() | nop();
}

yield procedure {:layer 1} foo2()
refines atomic_incr;
{
    call incr() | {:mark} nop() | nop();
}

atomic action {:layer 1,2} atomic_incr()
modifies x;
{
    x := x + 1;
}
yield procedure {:layer 1} incr();
refines atomic_incr;

atomic action {:layer 1,2} atomic_nop()
{
}
yield procedure {:layer 1} nop();
refines atomic_nop;
