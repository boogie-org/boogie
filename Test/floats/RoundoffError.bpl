// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_INT(int) returns (float24e8);
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_REAL(real) returns (float24e8);

procedure main() returns () {
  var tick : float24e8;
  var time : float24e8;
  var i: int;
  
  tick := TO_FLOAT32_INT(1)/TO_FLOAT32_INT(10);
  time := TO_FLOAT32_INT(0);
  
  i := 0;
  while (i < 10)
  {
    time := time + tick;
    i := i + 1;
  }
  assert time == TO_FLOAT32_INT(1);
}
