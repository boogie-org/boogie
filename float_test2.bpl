//Translation from addsub_float_exact.c
//Should Verify
procedure main() returns () {
	var x : float;
	var y : float;
	var z : float;
	var r : float;
	x := fp(1000000);
	y := x + fp(1);
	z := x - fp(1);
	r := y - z;
	assert r == fp(2);
}