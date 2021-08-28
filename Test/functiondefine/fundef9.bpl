// RUN: %parallel-boogie  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:define} foo(x:int) returns(int)
  { foo2(x) + 1 }
function {:define} foo2(x:int) returns(int)
  { foo(x) + 2 }

procedure test(x:int) returns (r:int)
  ensures r > 0;
{
  if (foo(x) > 0) {
    r := foo2(x);
  } else {
    r := 1;
  }
}
