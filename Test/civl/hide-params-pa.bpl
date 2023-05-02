// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

async action {:layer 2} SKIP () returns () { }

yield procedure {:layer 1} b ()
refines SKIP;
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

>-< action {:layer 1} A (i:int) returns (i':int)
{
  assert i > 0;
  assume i' > i;
}

// In the refinement checker for a, the remaining formals of A must be
// properly mapped to the matching formals in a.
yield procedure {:layer 0}
a ({:hide} b:bool, i:int, {:hide} r:real) returns ({:hide} b':bool, i':int, {:hide} r':real)
refines A;
{
  i' := i + 1;
}
