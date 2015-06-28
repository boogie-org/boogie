// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory -doModSetAnalysis "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure A({:linear_in "tid"} i': int) returns ({:linear "tid"} i: int);
  ensures i == i';

procedure B({:linear_in "tid"} i': int) returns ({:linear "tid"} i: int) 
{
  i := i';
  call i := A(i);
  assert false;
}

