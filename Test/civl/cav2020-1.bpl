// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x: int;
var {:layer 0,1} y: int;

procedure {:yields} {:layer 1} incr_x(_x: int)
requires {:layer 1} Inv(_x, x);
ensures {:layer 1} Inv(_x, x);
{
    call yield_x(_x);
    call _incr_x();
    call yield_x(_x);
    call _incr_x();
    call yield_x(_x);
}

procedure {:layer 1} {:yield_invariant} yield_x(_x: int);
requires Inv(_x, x);

procedure {:yields} {:layer 1} incr_y(_y: int)
requires {:layer 1} Inv(_y, y);
ensures {:layer 1} Inv(_y, y);
{
    call yield_y(_y);
    call _incr_y();
    call yield_y(_y);
    call _incr_y();
    call yield_y(_y);
}

procedure {:layer 1} {:yield_invariant} yield_y(_y: int);
requires Inv(_y, y);

procedure {:yields} {:layer 1} incr_x_y()
requires {:layer 1} Inv(0, x);
requires {:layer 1} Inv(0, y);
{
    par yield_x(0) | yield_y(0);
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

function {:inline} Inv(_a: int, a: int): bool
{
    _a <= a
}
