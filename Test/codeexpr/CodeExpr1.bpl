// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// ------ the good ------

procedure F(x: int, y: int) returns (z: bool)
  requires x < y;
  ensures z == (x < 3);
{
  start:
    z := |{ var a : bool, b : bool; B: a := x < 3; return a; }|;
    return;
}

function r(int): bool;

procedure F'(x: int, y: int) returns (z: bool)
{
  start:
    assume x < y;
    assume (forall t: int :: x < 3 + t ==> r(t));
    assert r(y);
}

procedure F''(x: int, y: int) returns (z: bool)
{
  start:
    assume x < y;
    assume (forall t: int :: |{ var a: bool;
                                Start:
                                a := x < 3 + t;
                                goto X, Y;
                                X: assume a; return r(t);
                                Y: assume !a; return true;
                             }|);
    assert r(y);
}

// ------ the bad ------

procedure G(x: int, y: int) returns (z: bool)
  requires x < y;
  ensures z == (x < 3);
{
  start:
    z := |{ var a : bool, b : bool; B: a := x < 3; return !a; }|;
    return;  // error: postcondition violation
}

procedure G'(x: int, y: int) returns (z: bool)
{
  start:
    assume x < y;
    assume (forall t: int :: x + 3 < t ==> r(t));
    assert r(y);  // error
}

procedure G''(x: int, y: int) returns (z: bool)
{
  start:
    assume x < y;
    assume (forall t: int :: |{ var a: bool;
                                Start:
                                a := x + 3 < t;
                                goto X, Y;
                                X: assume a; return r(t);
                                Y: assume !a; return true;
                             }|);
    assert r(y);  // error
}
