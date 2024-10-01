// RUN: %parallel-boogie /printSplit:%t /errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure IsolateReturn(x: int) returns (r: int)
  ensures r > 4
{
  z := 0;
  if (x > 0) {
    z := z + 1;
  } else {
    z := z + 2
  }
  
  if (y > 0) {
    z := z + 3;
    return {:isolate};
  }
  
  z := z + 4;
}

procedure IsolateReturnPath(x: int) returns (r: int)
  ensures r > 4
{
  z := 0;
  if (x > 0) {
    z := z + 1;
  } else {
    z := z + 2
  }
  
  if (y > 0) {
    z := z + 3;
    return {:isolate "path"};
  }
  
  z := z + 4;
}