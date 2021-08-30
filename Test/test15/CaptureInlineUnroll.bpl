// RUN: %boogie "%s" /mv:- /loopUnroll:2 /inline:none > "%t"
// RUN: %boogie "%s" /mv:- /loopUnroll:3 >> "%t"
// RUN: %diff "%s.expect" "%t"

procedure LoopUnroll(n: int)
{
  var i: int;

  assume {:captureState "procedure entry"} true;
  i := 0;
  while (i < n) {
    assume {:captureState "loop entry"} true;
    assert i != 2;  // error (with /loopUnroll:3 or higher)
    i := i + 1;
  }
  assume {:captureState "after loop"} true;
}

procedure Caller()
{
  var u: int;

  u := 0;
  assume {:captureState "0 calls"} true;

  call u := Increment(u);
  assume {:captureState "1 call"} true;

  u := u + 3;
  call u := Increment(u);
  assume {:captureState "2 calls"} true;

  assert u == 8;  // error
}

procedure {:inline 10} Increment(x: int) returns (y: int)
{
  assume {:captureState "Increment entry"} true;
  y := x + 1;
  assert y == 2;
  assume {:captureState "Increment exit"} true;
}
