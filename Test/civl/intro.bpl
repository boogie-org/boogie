// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 1,2} y:int;
var {:layer 0,1} x:int;

procedure {:atomic} {:layer 2,2} atomic_read_y () returns (v:int)
{ v := y; }

procedure {:atomic} {:layer 2,2} atomic_write_y (y':int)
modifies y;
{ y := y'; }

procedure {:yields} {:layer 1} {:refines "atomic_read_y"}  read_y () returns ({:layer 0,1} v:int)
requires {:layer 1} x == y;
{
  call v := read_x();
}

procedure {:yields} {:layer 1} {:refines "atomic_write_y"}  write_y (y':int)
requires {:layer 1} x == y;
{
  call write_x(y');
  call set_y_to_x();
}

procedure {:intro} {:layer 1} set_y_to_x ()
modifies y;
{
  y := x;
}

procedure {:atomic} {:layer 1,1} atomic_read_x () returns (v:int)
{ v := x; }

procedure {:atomic} {:layer 1,1} atomic_write_x (x':int)
modifies x;
{ x := x'; }

procedure {:yields} {:layer 0} {:refines "atomic_read_x"} read_x () returns ({:layer 0} v:int)
{
  call v := intro_read_x();
}

procedure {:yields} {:layer 0} {:refines "atomic_write_x"} write_x (x':int)
{
  call intro_write_x(x');
}

procedure {:intro} {:layer 0} intro_read_x () returns (v:int)
{ v := x; }

procedure {:intro} {:layer 0} intro_write_x (x':int)
modifies x;
{ x := x'; }
