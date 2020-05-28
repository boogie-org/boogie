// RUN: %boogie -proverLog:"%t1" -env:0 "%s"
// RUN: grep define "%t1" > "%t2"
// RUN: %diff "%s.expect" "%t2"

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
