// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 1,2} y:int;
var {:layer 0,1} x:int;

atomic action {:layer 2,2} atomic_read_y () returns (v:int)
{ v := y; }

atomic action {:layer 2,2} atomic_write_y (y':int)
modifies y;
{ y := y'; }

yield procedure {:layer 1} read_y () returns ({:layer 0,1} v:int)
refines atomic_read_y;
requires call Yield_xy();
{
  call v := read_x();
}

yield procedure {:layer 1} write_y (y':int)
refines atomic_write_y;
requires call Yield_xy();
{
  call write_x(y');
  call {:layer 1} y := Copy(x);
}

atomic action {:layer 1,1} atomic_read_x () returns (v:int)
{ v := x; }

atomic action {:layer 1,1} atomic_write_x (x':int)
modifies x;
{ x := x'; }

yield procedure {:layer 0} read_x () returns ({:layer 0} v:int)
refines atomic_read_x;
{
  call {:layer 0} v := Copy(x);
}

yield procedure {:layer 0} write_x (x':int)
refines atomic_write_x;
{
  call {:layer 0} x := Copy(x');
}

yield invariant {:layer 1} Yield_xy();
preserves x == y;
