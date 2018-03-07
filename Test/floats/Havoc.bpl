// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_REAL(real) returns (float53e11);

procedure double_range_true() returns () {
  var x : float53e11;
  havoc x;
  if (x >= TO_FLOAT64_REAL(-1e307) && x <= TO_FLOAT64_REAL(1e307)) {  
    assert(EQ(x,x));
  }
}

procedure double_range_false() returns () {
  var x : float53e11;
  havoc x;
  assert(EQ(x,x));
}

function {:builtin "fp.eq"} EQ(float53e11,float53e11) returns (bool);
