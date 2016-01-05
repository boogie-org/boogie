//Translation from inv_square_false-unreach-call.c
//Should Verify

procedure main() returns () {
	var x : float;
	var y : float;
	var z : float;
	
	havoc x;
	assume(x >= fp(-1) && x <= fp(1));
	
	if (x <= fp(-.00000000000000000001) || x >= fp(.00000000000000000001)) {
		y := x * x;
		assert(y != fp(0));
		z := fp(1) / y;
	}
}