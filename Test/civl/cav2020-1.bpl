// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x: int;
var {:layer 0,1} y: int;

procedure {:yields} {:layer 1}
{:yield_preserves "yield_x", _x}
incr_x(_x: int)
{
    call _incr_x();
    call yield_x(_x);
    call _incr_x();
}

procedure {:layer 1} {:yield_invariant} yield_x(_x: int);
requires _x <= x;

procedure {:yields} {:layer 1}
{:yield_preserves  "yield_y", _y}
incr_y(_y: int)
{
    call _incr_y();
    call yield_y(_y);
    call _incr_y();
}

procedure {:layer 1} {:yield_invariant} yield_y(_y: int);
requires _y <= y;

procedure {:yields} {:layer 1}
{:yield_requires "yield_x", 0}
{:yield_requires "yield_y", 0}
incr_x_y()
{
    if (*) {
        async call incr_x_y();
    }
    par incr_x(0) | yield_y(0);
    par incr_y(0) | yield_x(0);
    assert {:layer 1} 0 <= x && 0 <= y;
}

procedure {:layer 1,1} {:atomic} atomic_incr_x()
modifies x;
{
    x := x + 1;
}
procedure {:yields} {:layer 0} {:refines "atomic_incr_x"} _incr_x();

procedure {:layer 1,1} {:atomic} atomic_incr_y()
modifies y;
{
    y := y + 1;
}
procedure {:yields} {:layer 0} {:refines "atomic_incr_y"} _incr_y();
