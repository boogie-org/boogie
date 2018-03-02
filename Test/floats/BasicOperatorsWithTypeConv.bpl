// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_INT(int) returns (float24e8);
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_REAL(real) returns (float24e8);

procedure main() returns () {
  var x : float24e8;
  var y : float24e8;
  var z : float24e8;
  var r : float24e8;
  x := TO_FLOAT32_REAL(1e7);
  y := x + TO_FLOAT32_INT(1);
  z := x - TO_FLOAT32_INT(1);
  r := y - z;
  assert r == TO_FLOAT32_INT(2);
}
