//Translation from addsub_float_inexact.c
//Should give an error
procedure main() returns () {
	var x : float;
	var y : float;
	var z : float;
	var r : float;
	x := fp(10000000);
	y := x + fp(1);
	z := x - fp(1);
	r := y - z;
	assert r == fp(0);
}