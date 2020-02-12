// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// VC generation tests: passification

procedure good0(x: int) returns (y: int, z: int)
  ensures z == 4 || z == 4+x;
{
var t: int;
A:
  t := y;
  z := 3;
  goto B, C;
B:
  z := z + x;
  goto D;
C:
  goto D;
D:
  z := z + 1;
  y := t;
  return;
}

procedure good1(x: int) returns (y: int, z: int)
  ensures z == x + 4;
{
var t: int;
A:
  t := y;
  z := 3;
  z := z + x;
  z := z + 1;
  y := t;
  return;
}

procedure bad0(x: int) returns (y: int, z: int)
  ensures y == 4;  // ERROR: postcondition violation
{
var t: int;
A:
  t := z;
  z := 3;
  z := z + 1;
  y := t;
  return;
}

procedure Loop()
{
start:
  goto start;
}

procedure UnreachableBlock()
{
start:
  return;
notReached:
  goto start;
reallyNeverReached:
  goto reallyNeverReached;
}

procedure Loop0() returns (z: int)
  ensures 10 <= z;
{
var x: int;
A:
  goto B, C;
B:
  assume x < 10;
  x := x + 1;
  goto A;
C:
  assume !(x < 10);
  z := x;
  return;
}

const unique A0: name;
const unique A1: name;
const unique A2: name;

procedure Array0() returns (z: int)
  ensures z >= 5;
{
var a: [name,name]int;
L0:
  a[A0,A2] := 5;
  a[A0,A1] := 20;
  assert a[A0,A1] == 20;
  goto L1,L2;
L1:
  a[A0,A2] := 18;
  assert a[A0,A2] == 18;
  goto L2;
L2:
  assert a[A0,A1] == 20;
  z := a[A0,A2];
  return;
}

procedure Array1(o0: ref, o1: ref) returns (z: int)
  ensures z >= 5;
{
var a: [ref,name]int;
L0:
  a[o1,A0] := 5;
  a[o0,A0] := 20;
  assert a[o0,A0] == 20;
  goto L1,L2;
L1:
  a[o1,A0] := 18;
  assert a[o1,A0] == 18;
  goto L2;
L2:
  assert a[o0,A0] == 20;  // ERROR: assertion failure
  z := a[o1,A0];
  return;
}

procedure Array2(o0: ref, o1: ref) returns (z: int)
  ensures z >= 5;
{
var a: [ref,name]int;
L0:
  assume o1 != o0;
  a[o1,A0] := 5;
  a[o0,A0] := 20;
  assert a[o0,A0] == 20;
  goto L1,L2;
L1:
  a[o1,A0] := 18;
  assert a[o1,A0] == 18;
  goto L2;
L2:
  assert a[o0,A0] == 20;
  z := a[o1,A0];
  return;
}

procedure P()
{
var t: int;
L0:
  t := 0;
  goto L1, L2;
L1:
  t := 1;
  goto L2;
L2:
  assert t == 1;  // ERROR: assert failure
  return;
}

procedure Q()
{
var t: int;
L0:
  t := 0;
  goto L1, L2;
L1:
  t := 1;
  goto L2;
L2:
  assert t == 0;  // ERROR: assert failure
  return;
}

type name, ref;
