// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "(_ to_fp 8 24)"} TO_FLOAT32_INT(rmode, int) returns (float24e8);
function {:builtin "(_ to_fp 8 24)"} TO_FLOAT32_REAL(rmode ,real) returns (float24e8);
function {:builtin "(_ to_fp 8 24)"} TO_FLOAT32_BV32(rmode, bv32) returns (float24e8);
function {:builtin "(_ to_fp 11 53)"} TO_FLOAT64_BV64(rmode, bv64) returns (float53e11);
function {:builtin "(_ to_fp 8 24) RTN"} TO_FLOAT32_FLOAT64(float53e11) returns (float24e8);
function {:builtin "(_ to_fp 11 53) RTZ"} TO_FLOAT64_FLOAT32(float24e8) returns (float53e11);

procedure main() returns () {
  var i : int;
  var r : real;
  var f32 : float24e8;
  var f64 : float53e11;

  f32 := TO_FLOAT32_INT(RNA, 5);
  f32 := TO_FLOAT32_REAL(RTP, 5.0);

  f32 := TO_FLOAT32_BV32(RNE, 0bv32);
  f64 := TO_FLOAT64_BV64(RTN, 0bv64);

  f32 := TO_FLOAT32_FLOAT64(0x0.0e0f53e11);
  f64 := TO_FLOAT64_FLOAT32(0x0.0e0f24e8);

  f32 := TO_FLOAT32_FLOAT64(f64);
  f64 := TO_FLOAT64_FLOAT32(f32);

  return;
}

