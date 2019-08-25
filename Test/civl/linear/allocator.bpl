// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory -doModSetAnalysis "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;
function {:inline} {:linear "tid"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}

procedure A({:linear_in "tid"} i': int) returns ({:linear "tid"} i: int);
  ensures i == i';

procedure B({:linear_in "tid"} i': int) returns ({:linear "tid"} i: int) 
{
  i := i';
  call i := A(i);
  assert false;
}

