var a:int;

procedure Allocate() returns ({:linear "tid"} xls: int);

procedure {:entrypoint} {:yields} main() 
{
  var {:linear "tid"} i: int;
  var {:linear "tid"} j: int;
  call i := Allocate();
  call j := Allocate();
  par i := t(i) | j := t(j);
}

procedure {:yields} {:stable} t({:linear "tid"} i': int) returns ({:linear "tid"} i: int)
{
  i := i';
  call Yield();
  assert a == old(a);
  a := a + 1;
}

procedure {:yields} Yield()
{
  yield;
}
