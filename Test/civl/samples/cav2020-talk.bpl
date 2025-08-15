// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x: int;
var {:layer 0,1} y: int;

yield procedure {:layer 1} double_inc_x()
requires call yield_x(old(x));
ensures call yield_x(old(x) + 2);
{
    call inc_x();
    call yield_x(x);
    call inc_x();
}

yield invariant {:layer 1} yield_x(i: int);
preserves i <= x;

yield procedure {:layer 1} double_inc_y()
requires call yield_y(old(y));
ensures call yield_y(old(y) + 2);
{
    call inc_y();
    call yield_y(y);
    call inc_y();
}

yield invariant {:layer 1} yield_y(i: int);
preserves i <= y;

yield procedure {:layer 1} double_inc_x_y()
requires call yield_x(0);
requires call yield_y(0);
{
    call double_inc_x() | yield_y(y);
    call double_inc_y() | yield_x(x);
    assert {:layer 1} x >= 2 && y >= 2;
}

atomic action {:layer 1,1} atomic_inc_x()
modifies x;
{
    x := x + 1;
}
yield procedure {:layer 0} inc_x();
refines atomic_inc_x;

atomic action {:layer 1,1} atomic_inc_y()
modifies y;
{
    y := y + 1;
}
yield procedure {:layer 0} inc_y();
refines atomic_inc_y;
