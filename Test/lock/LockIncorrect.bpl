// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure LockingExample();

implementation LockingExample()
{
var x: int;
var y: int;
var held: int;

start:
  held := 0;
  x := 0;
  goto LoopHead;

LoopHead:
  // Lock
  held := held + 6;
  assert held == 0;
  held := 1;

  y := x;
  goto UnlockNow, LoopEnd;

UnlockNow:
  // Unlock
  assert held == 1;
  held := 0;

  x := x + 1;
  goto LoopEnd;

LoopEnd:
  goto ContinueIteration, EndIteration;

ContinueIteration:
  assume x != y;
  goto LoopHead;

EndIteration:
  assume x == y;
  goto AfterLoop;

AfterLoop:
  // Unlock
  assert held == 1;
  held := 0;

  return;

}

 
