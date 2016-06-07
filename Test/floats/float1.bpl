// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo(x : float<8, 24>) returns (r : float<8, 24>)
{
	r := fp(false, 1bv8, 0bv23);
	r := fp<8, 24>(1bv32);
	r := x;
	r := x + fp<8, 24>(1bv32);
	r := fp<8, 24>(1bv32) + fp<8, 24>(1bv32);
	assert(r == fp<8, 24>(2bv32));
	
	return;
}