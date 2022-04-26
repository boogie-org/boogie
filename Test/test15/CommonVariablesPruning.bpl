// VcsCores:1 means we only use a single solver for both procedures in this Boogie program.
// Prune triggers a full reset after using the solver on one problem
// RUN: %boogie "%s" -vcsCores:1 -normalizeNames:1 -prune -mv:- > "%t"
// RUN: %diff "%s.expect" "%t"

// Part of the MultiDimArray test from Dafny: https://github.com/dafny-lang/dafny/blob/cc913d9159ded2ad131c048135f817e49f500e50/Test/dafny0/MultiDimArray.dfy
// Useful to get the 'type' function in the captured model.
type A;
function Length<T>(a: [int]T): int;
const a: [int]int;
const b: [int]bool;

axiom Length(a) == 3;
axiom Length(b) == 5; 

procedure M0()
  ensures true;
{
  var x: bool;
  var y: int;
  assume {:captureState "before"} true;
  if (7 <= Length(a) && Length(a) <= Length(b)) {
    x := b[2];
    y := a[1];
    assume {:captureState "after"} true;
    assert x == b[2];
    assert y == a[1];
    assert false;
  }
}

// By verifying another procedure, we can see whether common variables are named again, which would trigger a name increment (like type@@0 instead of type)
procedure M1()
  ensures true;
{
  var x: bool;
  var y: int;
  assume {:captureState "before"} true;
  if (5 <= Length(a) && Length(a) <= Length(b)) {
    x := b[2];
    y := a[1];
    assume {:captureState "after"} true;
    assert x == b[2];
    assert y == a[1];
    assert false;
  }
}