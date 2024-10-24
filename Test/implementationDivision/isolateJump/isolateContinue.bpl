// RUN: %boogie /printSplit:- /errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure IsolateContinue(x: int) returns (r: int)
  requires x >= 10;
  ensures r >= 10;
{
  var i: int;
  i := x;
  r := 0;
  while(i > 0) 
    invariant r >= 10 - i;
  {
    i := i - 1;
    if (i == 3) {
      r := r + 2;
      goto {:isolate} Continue;
    }
    r := r + 1;
    Continue:
  }
}