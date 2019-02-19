// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type float = float24e8;

function {:builtin "fp.eq"} FEQ(float,float) returns (bool);

procedure Main()
{
  assert 0x0.0e0f24e8 != -0x0.0e0f24e8;
  assert FEQ(0x0.0e0f24e8,-0x0.0e0f24e8);
  assert 0+oo24e8 != 0-oo24e8;
  assert !FEQ(0+oo24e8,0-oo24e8);
}
