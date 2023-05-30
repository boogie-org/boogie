// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x: int;

yield invariant {:layer 1} Yield();

yield procedure {:layer 1} incr_by_two_bad()
refines atomic_incr_by_two;
{
    par incr() | incr() | Yield() | incr();
    call incr();
}

yield procedure {:layer 1} incr_by_two()
refines atomic_incr_by_two;
{
    par incr() | decr() | Yield() | incr();
    call incr();
}
both action {:layer 1,2} atomic_incr_by_two()
modifies x;
{
    x := x + 2;
}

both action {:layer 1,1} atomic_incr()
modifies x;
{
    x := x + 1;
}
yield procedure {:layer 0} incr();
refines atomic_incr;

both action {:layer 1,1} atomic_decr()
modifies x;
{
    x := x - 1;
}
yield procedure {:layer 0} decr();
refines atomic_decr;
