// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "fp.sqrt"} SQRT(rmode, float24e8) returns (float24e8);

procedure foo()
{
  var r : rmode;
  var a : float24e8;
  var b : float24e8;

  a := 0e127f24e8;

  r := RTN;
  b := SQRT(r, a);

  r := RTZ;
  b := SQRT(r, a);
}
