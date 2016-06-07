// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo(x : real) returns (r : float<8, 24>)
{
	r := 15;  // Error
	r := 15.0;  // Error
	r := fp(false, 1bv8, 0bv22); // Error
	r := fp<8, 23>(1bv31); // Error
	r := x; // Error
	r := fp<8, 23>(1bv31) + fp<8, 23>(1bv31); // Error
	r := fp<8, 24>(1bv32) + fp<8, 23>(1bv31); // Error
	
	return;
}