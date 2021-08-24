// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x: int;
var {:layer 0,1} y: int;

procedure {:yields} {:layer 1}
{:yield_requires "yield_x", old(x)}
{:yield_ensures  "yield_x", old(x) + 2}
double_inc_x()
{
    call inc_x();
    call yield_x(x);
    call inc_x();
}

procedure {:layer 1} {:yield_invariant} yield_x(i: int);
requires i <= x;

procedure {:yields} {:layer 1}
{:yield_requires "yield_y", old(y)}
{:yield_ensures  "yield_y", old(y) + 2}
double_inc_y()
{
    call inc_y();
    call yield_y(y);
    call inc_y();
}

procedure {:layer 1} {:yield_invariant} yield_y(i: int);
requires i <= y;

procedure {:yields} {:layer 1}
{:yield_requires "yield_x", 0}
{:yield_requires "yield_y", 0}
double_inc_x_y()
{
    par double_inc_x() | yield_y(y);
    par double_inc_y() | yield_x(x);
    assert {:layer 1} x >= 2 && y >= 2;
}

procedure {:layer 1,1} {:atomic} atomic_inc_x()
modifies x;
{
    x := x + 1;
}
procedure {:yields} {:layer 0} {:refines "atomic_inc_x"} inc_x();

procedure {:layer 1,1} {:atomic} atomic_inc_y()
modifies y;
{
    y := y + 1;
}
procedure {:yields} {:layer 0} {:refines "atomic_inc_y"} inc_y();
