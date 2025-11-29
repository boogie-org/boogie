// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X = int;
var {:layer 0,1} x:int;
var {:layer 0,1} y:bool;
////////////////////////////////////////////////////////////////////////////////

yield procedure {:layer 1} main ()
{
  call write_x_1(true);
}

atomic action {:layer 1,1} atomic_write_x_1 (x':bool)
modifies y;
{ y := x'; }

yield procedure {:layer 0} write_x_1 (y':bool);
refines atomic_write_x_1;

////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 1,1} atomic_write_x_2 (x':int, foo:int)
modifies x;
{ x := x'; }

yield procedure {:layer 0} write_x_2 (y':bool);
refines atomic_write_x_2;


////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 1,1} atomic_write_x_3 ({:linear} x':int)
modifies x;
{ x := x'; }

yield procedure {:layer 0} write_x_3 ({:linear_in} x':int);
refines atomic_write_x_3;

////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 1,1} atomic_write_x_4 (x':int)
modifies x;
{ x := x'; }

yield procedure {:layer 0} write_x_4 (x':bool);
refines atomic_write_x_4;
