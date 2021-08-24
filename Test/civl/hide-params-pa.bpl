// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:pending_async}{:datatype} PA;
function {:constructor} SKIP() : PA;

procedure {:atomic}{:layer 2} SKIP () returns () { }

procedure {:yields}{:layer 1}{:refines "SKIP"} b ()
{
  var {:layer 0} b:bool;
  var {:layer 0} b':bool;
  var i:int;
  var i':int;
  var {:layer 0} r:real;
  var {:layer 0} r':real;

  i := 1;
  call b', i', r' := a(b, i, r);
  // at layer 1 this call must be rewritten to
  // call i', returnedPAs := A(i);
}

procedure {:atomic}{:layer 1} A (i:int) returns (i':int, {:pending_async} PAs:[PA]int)
{
  assert i > 0;
  PAs := (lambda pa:PA :: 0);
  assume i' > i;
}

// In the refinement checker for a, the remaining formals of A must be
// properly mapped to the matching formals in a.
procedure {:yields}{:layer 0}{:refines "A"}
a ({:hide} b:bool, i:int, {:hide} r:real) returns ({:hide} b':bool, i':int, {:hide} r':real)
{
  i' := i + 1;
}
