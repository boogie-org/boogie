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


procedure StructuredLockingExample()
{
  var x: int;
  var y: int;
  var held: bool;

  held := false;
  x := 0;

  while (true)
    invariant !held;
  {
    // Lock
    assert !held;
    held := true;

    y := x;
    if (*) {
      // Unlock
      assert held;
      held := false;

      x := x + 1;
    }

    if (x == y) { break; }
  }

  // Unlock
  assert held;
  held := false;
}

procedure StructuredLockingExampleWithCalls()
{
  var x: int;
  var y: int;
  var mutex: Mutex;

  call mutex := Initialize();
  x := 0;

  while (true)
    invariant !IsHeld(mutex);
  {
    call mutex := Acquire(mutex);

    y := x;
    if (*) {
      call mutex := Release(mutex);
      x := x + 1;
    }

    if (x == y) { break; }
  }

  call mutex := Release(mutex);
}

type Mutex;
function IsHeld(Mutex) returns (bool);

procedure Initialize() returns (post: Mutex);
  ensures !IsHeld(post);

procedure Acquire(pre: Mutex) returns (post: Mutex);
  requires !IsHeld(pre);
  ensures IsHeld(post);

procedure Release(pre: Mutex) returns (post: Mutex);
  requires IsHeld(pre);
  ensures !IsHeld(post);
