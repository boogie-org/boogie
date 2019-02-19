// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type fl = float24e8;
type float = fl;
type do = float53e11;
type double = do;


procedure foo(x : double) returns (r : float)
{
  r := 0x2.0e0f24e8;
  r := 0x1.000002e0f24e8;
  r := x; //Error
  r := x * 0x1.000002e0f24e8; //Error
  r := x + 0x1.000002e0f24e8; //Error
  r := 0x1.0e0f24e8 + 0x1.0e0f24e8;
  assert(r == 0x2.0e0f24e8);
  
  return;
}
