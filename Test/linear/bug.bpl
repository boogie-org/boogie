function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;
function {:inline} {:linear ""} LinearIntDistinctness(x:int) : [int]bool { MapConstBool(false)[x := true] }

var {:linear ""} g:int;

procedure A()
{
}

procedure B()
{
  call A();
  assert false;
}
