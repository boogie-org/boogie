// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"




type {:linear "tid"} X = int;

procedure A({:linear_in "tid"} i': int) returns ({:linear "tid"} i: int);
  ensures i == i';

procedure B({:linear_in "tid"} i': int) returns ({:linear "tid"} i: int)
{
  i := i';
  call i := A(i);
  assert false;
}
