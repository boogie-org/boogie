// RUN: %parallel-boogie /trace /vcsMaxSplits:2 /vcsMaxCost:0 "%s" > %t.log
// RUN: %OutputCheck --file-to-check "%t.log" "%s"
// CHECK-L: checking split 1/2, 0.00%, (cost:17/2)

procedure SumFour(a: int, b: int, c: int, d: int) returns (e: int)
  ensures e == a + b + c + d;
{
  var ab: int;
  var abc: int; 
  ab := b + a;
  assert ab == a + b;
  abc := ab + c;
  assert abc == a + b + c;
  e := abc + d;
  assert e == a + b + c + d;
  return;
}