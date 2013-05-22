var a:int;

procedure Allocate() returns ({:linear "tid"} xls: int);

procedure {:entrypoint} main() 
{
  var {:linear "tid"} i: int;
  var {:linear "tid"} j: int;
  call i := Allocate();
  call j := Allocate();
  call i := t(i) | j := t(j);
}

procedure t({:linear "tid"} i': int) returns ({:linear "tid"} i: int)
{
  i := i';
  call Yield();
  assert a == old(a);
  a := a + 1;
}

procedure Yield()
{
  yield;
}
