// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Inc2(x: int): int {
  (var x' := x + 4; x' - 2)
}

procedure {:inline 1} Inc3(x: int) returns (y: int) {
  y := (var y' := x + 3; y');
}

procedure P() {
  var x: int;
  var b: bool;

  x := 10;
  call x := Inc3(Inc2(x + 3));
  assert x == 18;

  b := (var y := x; (var y' := y + 1; (forall x': int :: x' == y' ==> x' == 19)));
  assert b;
  b := (var y := x; (forall x': int :: x' == y ==> (var x'' := x' + 20; x'' == 38)));
  assert b;
  b := (var y := x; (exists x': int :: x' < y && x' == 28));
  assert !b;
}


function ShadowInc2(x: int): int {
  (var x := x + 4; x - 2)
}

procedure {:inline 1} ShadowInc3(x: int) returns (y: int)
{
  y := (var y := x + 3; y);
}

procedure ShadowP() {
  var x: int;
  var b: bool;

  x := 10;
  call x := ShadowInc3(ShadowInc2(x + 3));
  assert x == 18;

  b := (var y := x; (var y := y + 1; (forall x: int :: x == y ==> x == 19)));
  assert b;
  b := (var y := x; (forall x: int :: x == y ==> (var x := x + 20; x == 38)));
  assert b;
  b := (var y := x; (exists x: int :: x < y && x == 28));
  assert !b;
}
