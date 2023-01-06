// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "lin"} X = int;
var {:layer 0,1} x:int;
var {:layer 0,1} y:bool;
////////////////////////////////////////////////////////////////////////////////

procedure {:yields} {:layer 1} main ()
{
  call write_x_1(true);
}

procedure {:atomic} {:layer 1,1} atomic_write_x_1 (x':bool)
modifies y;
{ y := x'; }

procedure {:yields} {:layer 0} {:refines "atomic_write_x_1"} write_x_1 (y':bool);

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic} {:layer 1,1} atomic_write_x_2 (x':int, foo:int)
modifies x;
{ x := x'; }

procedure {:yields} {:layer 0} {:refines "atomic_write_x_2"} write_x_2 (y':bool);


////////////////////////////////////////////////////////////////////////////////

procedure {:atomic} {:layer 1,1} atomic_write_x_3 ({:linear "lin"} x':int)
modifies x;
{ x := x'; }

procedure {:yields} {:layer 0} {:refines "atomic_write_x_3"} write_x_3 ({:linear_in "lin"} x':int);

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic} {:layer 1,1} atomic_write_x_4 (x':int)
modifies x;
{ x := x'; }

procedure {:yields} {:layer 0} {:refines "atomic_write_x_4"} write_x_4 (x':bool);
