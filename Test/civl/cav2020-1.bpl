// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x: int;
var {:layer 0,1} y: int;

yield procedure {:layer 1} incr_x(_x: int)
preserves call yield_x(_x);
{
    call _incr_x();
    call yield_x(_x);
    call _incr_x();
}

yield invariant {:layer 1} yield_x(_x: int);
invariant _x <= x;

yield procedure {:layer 1} incr_y(_y: int)
preserves call yield_y(_y);
{
    call _incr_y();
    call yield_y(_y);
    call _incr_y();
}

yield invariant {:layer 1} yield_y(_y: int);
invariant _y <= y;

yield procedure {:layer 1} incr_x_y()
requires call yield_x(0);
requires call yield_y(0);
{
    if (*) {
        async call incr_x_y();
    }
    par incr_x(0) | yield_y(0);
    par incr_y(0) | yield_x(0);
    assert {:layer 1} 0 <= x && 0 <= y;
}

action {:layer 1,1} atomic_incr_x()
modifies x;
{
    x := x + 1;
}
yield procedure {:layer 0} _incr_x();
refines atomic_incr_x;

action {:layer 1,1} atomic_incr_y()
modifies y;
{
    y := y + 1;
}
yield procedure {:layer 0} _incr_y();
refines atomic_incr_y;
