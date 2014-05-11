// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory %s > %t
// RUN: %diff %s.expect %t
const {:existential true} b0: bool;
const {:existential true} b1: bool;
const {:existential true} b2: bool;

var x:int;

procedure A()
{
  x := x + 1;
  yield;
}

procedure B()
{
  x := 5;
  yield;
  assert b0 ==> (x == 5);
  assert b1 ==> (x >= 5);
  assert b2 ==> (x >= 6);
}

