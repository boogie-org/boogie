// RUN: %parallel-boogie -proverLog:"%t.smt2" -env:0 "%s"
// RUN: %OutputCheck "%s" --file-to-check="%t.smt2"

// CHECK-L:(define-fun foo2 ((x Int) ) Int (+ x 1))
// CHECK-L:(define-fun foo ((x@@0 Int) ) Bool (> (foo2 x@@0) 0))
function {:define} foo(x:int) returns(bool)
  { foo2(x) > 0 }
function {:define} foo2(x:int) returns(int)
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
