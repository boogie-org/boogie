// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// This file has been created to test some of the formula/term issues in Zap.
// However, the test harness does not specify any particular prover to be used,
// since these tests should pass regardless of which prover is used.

procedure P()
{
  var a: int, b: int, t: bool;

  start:
    assume a == b;
    t := a == b;
    assert t;
    return;
}

function f(bool) returns (int);
const A: int;
const B: int;

axiom f(A < B) == 5;

procedure Q()
{
  start:
    assume A < B;
    assert f(true) == 5;
    return;
}

// ----- and now some erroneous procedures

procedure PX()
{
  var a: int, b: int, t: bool;

  start:
    assume a == b;
    t := a == b;
    assert !t;  // error
    return;
}

procedure QX()
{
  start:
    assume A < B;
    assert f(true) < 2;  // error
    return;
}
