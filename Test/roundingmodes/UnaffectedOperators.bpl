// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "fp.add"} ADD(rmode, float24e8, float24e8) returns (float24e8);
function {:builtin "fp.sub"} SUB(rmode, float24e8, float24e8) returns (float24e8);
function {:builtin "fp.mul"} MUL(rmode, float24e8, float24e8) returns (float24e8);
function {:builtin "fp.div"} DIV(rmode, float24e8, float24e8) returns (float24e8);

procedure foo(a : float24e8, b : float24e8)
requires b != 0x0.0e0f24e8;
{
  var c : float24e8;
  var d : float24e8;

  c := a + b;
  d := ADD(RNE, a, b);
  assert (c == d);

  c := a - b;
  d := SUB(RNE, a, b);
  assert (c == d);

  c := a * b;
  d := MUL(RNE, a, b);
  assert (c == d);

  c := a / b;
  d := DIV(RNE, a, b);
  assert (c == d);

}
