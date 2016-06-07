// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const a: [int]bool;

// element 5 of a stores the value true
axiom a == a[5 := true];

procedure P()
{
  assert a[5];
}

procedure Q()
{
  assert a[4];  // error
}

procedure R()
{
  assert !a[5];  // error
}

procedure S(y: int, t: bool)
  requires y <= 5;
{
  if (a[y := t][5] == false) {
    assert y == 5;
  }
}

procedure T0(aa: [int,ref]bool)
{
  assert aa[5,null := true] != aa[2,null := false];  // error
}

procedure T1(aa: [int,ref]bool)
  requires aa[5,null] && !aa[2,null];
{
  assert aa[5,null := true] == aa[2,null := false];  // error, because we have no extensionality
}

procedure T2(aa: [int,ref]bool)
  requires aa[5,null] && !aa[2,null];
{
  assert (forall x: int, y: ref :: aa[5,null := true][x,y] == aa[2,null := false][x,y]);
}

procedure U0(a: [int]int)
{
  var b: [int]int;

  b := a[5 := 12];
  assert a == b;  // error
}

procedure U1() returns (a: [int]int)
{
  var b: [int]int;

  b := a[5 := 12];
  a[5] := 12;
  assert a == b;
}

type Field a;
const unique IntField: Field int;
const unique RefField: Field ref;
const unique SomeField: Field int;

procedure FieldProc(H: <a>[ref,Field a]a, this: ref)
{
  var i: int, r: ref, y: any;
  var K: <a>[ref,Field a]a;

  K := H[this, IntField := 5][this, RefField := null][this, SomeField := 100][this, IntField := 7];
  assert K[this, IntField] == 7;
  assert K[this, RefField] == null;
  assert K[this, SomeField] == 100;
}

type ref, any;
const null : ref;
