// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "tid"} X = int;

procedure A() {}

procedure B({:linear_in "tid"} tid:int) returns({:linear "tid"} tid':int)
{
  tid' := tid;
  call A();
}

