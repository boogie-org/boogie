//Translation from loop.c
//Should return an error?  (The real case does as well...)

procedure main() returns () {
	var x : float;
	var y : float;
	var z : float;
	
	x := fp(1);
	y := fp(10000000);
	z := fp(42);
	
	while (x < y) {
		x := x + fp(1);
		y := y - fp(1);
		z := z + fp(1);
	}
	
	assert(z >= fp(0) && z <= fp(10000000));
}