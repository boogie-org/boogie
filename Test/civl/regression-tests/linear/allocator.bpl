// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure A({:linear_in} i': int) returns ({:linear} i: int);
  ensures i == i';

procedure B({:linear_in} i': int) returns ({:linear} i: int)
{
  i := i';
  call i := A(i);
  assert false;
}
