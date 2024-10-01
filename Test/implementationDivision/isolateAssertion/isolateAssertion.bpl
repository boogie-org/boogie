// RUN: %parallel-boogie /printSplit:%t /errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure IsolateAssertion(x: int, y: int)
{
  var z: int;
  z := 0;
  if (x > 0) {
    z := z + 1;
  } else {
    z := z + 2;
  }
  
  if (y > 0) {
    z := z + 3;
  } else {
    z := z + 4;
  }
  assert z > 1;
  assert {:isolate} z > 2;
  assert z > 3;
}

procedure IsolatePathsAssertion(x: int, y: int)
{
  var z: int;
  z := 0;
  if (x > 0) {
    z := z + 1;
  } else {
    z := z + 2;
  }
  
  if (y > 0) {
    z := z + 3;
  } else {
    z := z + 4;
  }
  assert z > 1;
  assert {:isolate "paths"} z > 2;
  assert z > 3;
}