//Translation from addsub_double_exact.c
//Should Verify
procedure main() returns () {
	var x : float(11 53);
	var y : float(11 53);
	var z : float(11 53);
	var r : float(11 53);
	x := fp(10000000 11 53);
	y := x + fp(1 11 53);
	z := x - fp(1 11 53);
	r := y - z;
	assert r == fp(2 11 53);
}