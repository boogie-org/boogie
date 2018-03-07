// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "fp.add" :rm "RNE"} ADD(float24e8, float24e8) returns (float24e8);

procedure foo()
{
  var a : float24e8;
  var b : float24e8;

  a := 0e127f24e8;
  b := 0e127f24e8;
  b := ADD(a, b);
  assert (b == 0e128f24e8);
}
