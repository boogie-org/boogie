// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const unique f1 : Field int;
const unique f2 : Field bv32;
const unique f3 : Field bool;

const unique r1 : ref;
const unique r2 : ref;

var H : <x>[ref,Field x]x;

procedure foo()
  modifies H;
{
  var i : int;
  var b : bv32;
  var c : bool;

  H[r1, f1] := 3;
  H[r1, f2] := 77bv32;
  H[r1, f3] := true;
  i := H[r1,f1];
  b := H[r1,f2];
  c := H[r1,f3];
  assert i == 3;
  assert b == 77bv32;
  assert H[r1,f3];
}

var B : [bv32]bv32;

procedure bar()
  modifies B;
{
  var b : bv32;

  B[42bv32] := 77bv32;
  b := B[42bv32];
  assert b == 77bv32;
}


type Field a, ref;