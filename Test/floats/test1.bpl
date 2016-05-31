//Translation from addsub_double_exact.c
//Should Verify
procedure main() returns () {
	var x : float<11, 53>;
	var y : float<11, 53>;
	var z : float<11, 53>;
	var r : float<11, 53>;
	x := fp<11, 53> (10000000bv64);
	y := x + fp<11, 53>(1bv64);
	z := x - fp<11, 53>(1bv64);
	r := y - z;
	assert r == fp<11, 53> (2bv64);
}