// RUN: %boogie  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:define} foo(x:int) returns(bool)
  { foo2(x) > 0 }
function {:define} {:inline} foo2(x:int) returns(int)
  { x + 1 }

procedure test(x:int) returns (r:int)
  ensures r > 0;
{
  if (foo(x)) {
    r := foo2(x);
  } else {
    r := 1;
  }
}
