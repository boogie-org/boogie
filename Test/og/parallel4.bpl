var {:phase 1} a:int;

procedure Allocate() returns ({:linear "tid"} xls: int);

function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;
function {:inline} {:linear "tid"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}

procedure {:yields} {:phase 1} main() 
{
  var {:linear "tid"} i: int;
  var {:linear "tid"} j: int;
  call i := Allocate();
  call j := Allocate();
  par i := t(i) | j := t(j);
}

procedure {:yields} {:phase 1} t({:linear "tid"} i': int) returns ({:linear "tid"} i: int)
{
  i := i';
  call Yield();
  assert {:phase 1} a == old(a);
  call Incr();
  yield;
}

procedure {:yields} {:phase 0,1} Incr();
ensures {:atomic} |{A: a := a + 1; return true; }|;

procedure {:yields} {:phase 1} Yield()
{
  yield;
}
