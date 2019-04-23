// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "fp.mul RNA"} MUL_RNA(float24e8, float24e8) returns (float24e8);

procedure foo()
{
  var r : rmode;
  var a : float24e8;
  var b : float24e8;

  a := 0x1.0e0f24e8;
  b := 0x1.0e0f24e8;

  b := MUL_RNA(a, b);
}
