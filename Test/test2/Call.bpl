// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure Bar() returns (barresult: ref);

procedure Foo();

implementation Foo()
{
  var x: ref;

  entry:
    call x := Bar();
    assume x == null;
    call x := Bar();
    assert x == null;
    return;

}

procedure DifferentFormalNames(x: int, y: int) returns (z: int);
  requires x < y;
  ensures z == x;

implementation DifferentFormalNames(x: int, y: int) returns (z: int)
{
  start:
    assert x < y;
    z := x;
    return;
}

implementation DifferentFormalNames(y: int, x: int) returns (w: int)
{
  start:
    goto A, B;
  A:
    assert y < x;
    assume false;
    return;
  B:
    w := y;
    return;
}

implementation DifferentFormalNames(y: int, x: int) returns (w: int)
{
  start:
    assert x < y;  // error
    w := y;
    return;
}

implementation DifferentFormalNames(y: int, x: int) returns (w: int)
{
  start:
    w := x;
    return;  // error: postcondition violation
}

type ref;

const null : ref;
