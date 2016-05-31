//Translation from nan_double_range_true-unreach-call.c
//Should verify
//Uggghhhh, should I add support for e?

procedure main() returns () {
	var x : float(11 53);
	havoc x;
	if (x >= fp(-100000000000000000000000000 11 53) && x <= fp(100000000000000000000000000 11 53)) {	
		assert(x==x);
	}
}