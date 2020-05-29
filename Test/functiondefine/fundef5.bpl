// RUN: %boogie -proverLog:"%t1" -env:0 "%s"
// RUN: grep define "%t1" > "%t2"
// RUN: %diff "%s.expect" "%t2"

function {:define true} foo(x:int) returns(bool)
  { foo2(x) > 0 }
function {:define true} foo2(x:int) returns(int)
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
