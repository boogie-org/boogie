//Translation from inv_square_false-unreach-call.c
//Should return an error (without crashing)

procedure main() returns () {
	var x : float;
	var y : float;
	var z : float;
	
	havoc x;
	assume(x >= fp(-1) && x <= fp(1));
	
	if (x != fp(0)) {
		y := x * x;
		assert(y != fp(0));
		z := fp(1) / y;
	}
}