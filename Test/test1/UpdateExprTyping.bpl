// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure P(a: [int]bool, b: [int]ref, c: [bool]bool)
{
  assert a == b;  // type error
  assert a == c;  // type error

  assert a == a[5 := true];
  assert a == a[true := true];  // type error
  assert a == a[5 := 5]; // type error in RHS
  assert a == b[5 := null];  // type error
}

procedure Q(aa: [int,ref]bool)
{
  assert aa[5,null := true] != aa[2,null := false];
  assert aa == aa[null,null := true];  // type error, index 0
  assert aa == aa[5,true := true];  // type error, index 1
  assert aa == aa[5,null := null];  // type error, RHS
}

type Field a;
const unique IntField: Field int;
const unique RefField: Field ref;
const unique SomeField: Field any;

procedure R(H: <x>[ref,Field x]x, this: ref)
{
  var i: int, r: ref, y: any;
  var K: <wz>[ref,Field wz]wz;

  i := H[this, IntField];
  r := H[this, RefField];
  y := H[this, IntField];       // type error, wrong LHS
  y := H[this, SomeField];

  K := H[this, IntField := i][this, RefField := r][this, SomeField := y];
  K := H[this, SomeField := r]; // type error, wrong RHS

  K := K[this, IntField := r];  // RHS has wrong type (ref, expecting int)
  K := K[this, RefField := i];  // RHS has wrong type (int, expecting ref)
}

type ref, any;
const null : ref;
