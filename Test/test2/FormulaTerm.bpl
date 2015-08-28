// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Test formula-term distinction in Simplify

procedure plus(x: int, y: int) returns (z: int);
  ensures z == x + y;

implementation plus(x: int, y: int) returns (z: int)
{
start:
  assume z == 3;
  return;  // ERROR: postcondition possibly violated
}

implementation plus(x: int, y: int) returns (z: int)
{
start:
  z := x + y;
  return;
}

implementation plus(x: int, y: int) returns (z: int)
{
start:
  z := x + y;
  z := 0 + z;
  return;
}

procedure plus2(x: int, y: int) returns (z: int)
  ensures z == x + y;
{
start:
  z := x + y;
  return;
}

procedure or(x: int, y: int, a: int, b: int) returns (z: int)
  requires a == b;
{
var t: bool;
start:
  t := (x < y || x > y || x == y || x != y) && a >= b && a <= b;
  assert (x < y || x > y || x == y || x != y) && a >= b && a <= b;
  assert t;
  return;
}

procedure less(x: int, y: int) returns (z: bool);
  requires x < y;
  ensures z == (x < y);

implementation less(x: int, y: int) returns (z: bool)
{
start:
  z := x < y;
  return;
}

implementation less(x: int, y: int) returns (z: bool)
{
start:
  goto yes, no;
yes:
  assume x < y;
  z := true;
  return;
no:
  assume !(x < y);
  z := false;
  return;
}

implementation less(x: int, y: int) returns (z: bool)
{
start:
  goto yes, no;
yes:
  assume x < y;
  z := true;
  return;
no:
  assume x >= y;
  z := false;
  return;
}

procedure LESS(x: int, y: int) returns (z: bool);
  requires x < y;
  ensures z <==> (x < y);

implementation LESS(x: int, y: int) returns (z: bool)
{
start:
  z := x < y;
  return;
}

implementation LESS(x: int, y: int) returns (z: bool)
{
start:
  goto yes, no;
yes:
  assume x < y;
  z := true;
  return;
no:
  assume !(x < y);
  z := false;
  return;
}

implementation LESS(x: int, y: int) returns (z: bool)
{
start:
  goto yes, no;
yes:
  assume x < y;
  z := true;
  return;
no:
  assume x >= y;
  z := false;
  return;
}

procedure Assignments()
{
  var b: bool;
  var c: bool;
  var d: bool;
  var x: bool, y: bool;

  entry:
    b := c || d;
    b := c && d;
    x := c <==> d;
    y := c ==> d;
    assert x ==> y;
    return;
}
