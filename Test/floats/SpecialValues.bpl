// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo() returns (r : float24e8) {
  var d : float53e11;

  r := 0NaN24e8;
  r := 0nan24e8;
  assert !FEQ(r,0NaN24e8);  //NaN != NaN
  r := 0+oo24e8;
  r := 0-oo24e8;
  r := 0x1.0e32f24e8; //Error: this is a synonym for +oo, which is disallowed
  r := -0x1.0e32f24e8; //Error: this is a synonym for -oo, which is disallowed
  r := -0x5.0e32f24e8; //Error: NaN values are disallowed

  d := 0NaN53e11;
  d := 0nan53e11;
  assert !DEQ(d,0NaN53e11);
  d := 0+oo53e11;
  d := 0-oo53e11;
  d := 0;
  d := 0x1.0e256f53e11;
  d := -0x1.0e256f53e11;
  d := -0x5.0e256f53e11;

  d := 0+zero53e11; //Error: there are no longer special values for +zero and -zero
  d := 0-zero53e11;

  d := 0x0.0e0f53e11;
  assert d == 0x0.0e0f53e11;
  d := -0x0.0e0f53e11;
  assert d == -0x0.0e0f53e11;
  assert(DEQ(0x0.0e0f53e11, -0x0.0e0f53e11));

  return;
}

function {:builtin "fp.eq"} FEQ(float24e8,float24e8) returns (bool);
function {:builtin "fp.eq"} DEQ(float53e11,float53e11) returns (bool);
