// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo(x : real) returns (r : float8e24)
{
	r := 15;  // Error
	r := 15.0;  // Error
	r := 0e1f22e8; // Error
	r := 1e0f23e8; // Error
	r := x; // Error
	r := 1e0f23e8 + 1e0f23e8; // Error
	r := 1e0f24e8 + 1e0f23e8; // Error
	
	return;
}