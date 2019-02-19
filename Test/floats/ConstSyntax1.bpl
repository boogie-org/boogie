// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo(x : real) returns (r : float8e24)
{
  r := 15;  // Error
  r := 15.0;  // Error
  r := 0x4.0e-32f22e8; // Error
  r := 0x0.00001e-32f23e8; // Error
  r := x; // Error
  r := 0x0.00001e-32f23e8 + 0x0.00001e-32f23e8; // Error
  r := 0x0.000008e-32f24e8 + 0x0.00001e-32f23e8; // Error
  
  return;
}
