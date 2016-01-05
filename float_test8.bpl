//Translation from float_double.c
//Should Verify
//FAILS: I don't have this functionality yet...

procedure main() returns () {
	var x : float(11 53);
	var y : float;
	
	x := fp(100000000000000000001 11 53);
	y := x;
	assert(x != y);
}