// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 1,2} y:int;
var {:layer 0,1} x:int;

action {:layer 2,2} atomic_read_y () returns (v:int)
{ v := y; }

action {:layer 2,2} atomic_write_y (y':int)
modifies y;
{ y := y'; }

yield procedure {:layer 1} read_y () returns ({:layer 0,1} v:int) refines atomic_read_y
requires call Yield_xy();
{
  call v := read_x();
}

yield procedure {:layer 1} write_y (y':int) refines atomic_write_y
requires call Yield_xy();
{
  call write_x(y');
  call set_y_to_x();
}

link action {:layer 1} set_y_to_x ()
modifies y;
{
  y := x;
}

action {:layer 1,1} atomic_read_x () returns (v:int)
{ v := x; }

action {:layer 1,1} atomic_write_x (x':int)
modifies x;
{ x := x'; }

yield procedure {:layer 0} read_x () returns ({:layer 0} v:int) refines atomic_read_x
{
  call v := intro_read_x();
}

yield procedure {:layer 0} write_x (x':int) refines atomic_write_x
{
  call intro_write_x(x');
}

link action {:layer 0} intro_read_x () returns (v:int)
{ v := x; }

link action {:layer 0} intro_write_x (x':int)
modifies x;
{ x := x'; }

yield invariant {:layer 1} Yield_xy();
invariant x == y;
