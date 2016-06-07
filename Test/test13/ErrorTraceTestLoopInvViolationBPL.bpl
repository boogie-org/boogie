// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// simple assert
procedure asserting() {
  var x: int;

  x := 0;

  assert x == 1;
}

// invariant failing initially
procedure loopInvInitiallyViolated(y: int) {
  var x: int;

  x := y;

  while (true) invariant (x == 1); {
    x := 1;
  }
}

// invariant failing after iteration
procedure loopInvMaintenanceViolated() {
  var x: int;

  x := 0;

  while (true)  invariant x == 0; {
    x := 1;
  }
}
