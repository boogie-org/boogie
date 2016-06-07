// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure main() returns () {
	var x : float32;
	var y : float32;
	var z : float32;
	
	z := x + y;
	z := x - y;
	z := x * y;
	assume(y != fp<8, 24>(0bv32));
	z := x / y;
	
	z := (fp<8, 24>(1bv32) + fp<8, 24>(1bv32)) + fp<8, 24>(0bv32);
	assert(z == fp<8, 24>(2bv32));
	
	z := fp<8, 24>(2bv32) - fp<8, 24>(1bv32);
	assert(z == fp<8, 24>(1bv32));
	
	z := fp(false, 127bv8, 0bv23) * fp(false, 127bv8, 0bv23);
	assert(z == fp(false, 127bv8, 0bv23));
	
	z := fp<8, 24>(1bv32) / fp<8, 24>(1bv32);
	assert(z == fp(false, 127bv8, 0bv23));
	
	return;
}