// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type float = float24e8;
type f = float;

procedure foo(x : float) returns (r : f)
{
  r := 0x2.0e0f24e8;
  r := 0x1.000002e0f24e8;
  r := x;
  r := x * 0x1.000002e0f24e8;
  r := x + 0x1.000002e0f24e8;
  r := 0x1.0e0f24e8 + 0x1.0e0f24e8;
  assert(r == 0x2.0e0f24e8);
  
  return;
}
