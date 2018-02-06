// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_FLOAT32(float24e8) returns (float53e11);
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_FLOAT64(float53e11) returns (float24e8);
function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_INT(int) returns (float53e11);
function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_REAL(real) returns (float53e11);

procedure main() returns () {
  var x : float53e11;
  var y : float24e8;
  
  x := TO_FLOAT64_REAL(1e20)+TO_FLOAT64_INT(1);
  y := TO_FLOAT32_FLOAT64(x);
  assert x != TO_FLOAT64_FLOAT32(y);
}
