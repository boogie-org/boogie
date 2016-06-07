// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure main() returns () {
	var x : float32;
	var y : float32;
	var z : float32;
	var r : float32;
	x := fp<8, 24>(3221225472bv32);
	y := x + fp<8, 24>(1bv32);
	z := x - fp<8, 24>(1bv32);
	r := y - z;
	assert r == fp<8, 24>(2bv32);
}