// RUN: %boogie  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:define} foo(x:int) returns(bool)
  { foo2(x, x) > 0 }
function {:define} foo2(x:int, y:int) returns(int)
  { x + y }

procedure test(x:int) returns (r:int)
  ensures r > 0;
{
  if (foo(x)) {
    r := foo2(x, x);
  } else {
    r := 1;
  }
}

procedure test1(x:int) returns (r:int)
  ensures r > 0;
{
  if (foo(x)) {
    r := foo2(x, -x);
  } else {
    r := 1;
  }
}
