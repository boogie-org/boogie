// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;
var y: bool;

procedure one() 
{
  var n: int;
  n := 10;
  while(n >= 1)
  measure n;
  measure y;
  {
      n := n - 1;
  }
}
