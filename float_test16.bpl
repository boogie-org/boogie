//Translation from nan_double_false-unreach-call.c
//Should return an error

procedure main() returns () {
	var x : float(11 53);
	havoc x;
	assert(x==x);
}