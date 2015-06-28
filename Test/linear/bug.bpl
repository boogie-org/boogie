// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory -doModSetAnalysis "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
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
