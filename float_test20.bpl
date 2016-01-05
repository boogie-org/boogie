//Should return an error?
//Translation from Rump_double.c

procedure main() returns () {
	var x : float(11 53);
	var y : float(11 53);
	var r : float(11 53);
	
	x := fp(77617 11 53);
	y := fp(33096 11 53);
	r := y*y*y*y*y*y * fp(333.75 11 53) + x*x * (x*x*y*y*fp(11 11 53) - y*y*y*y*y*y - y*y*y*y * fp(121 11 53) - fp(2 11 53)) + y*y*y*y*y*y*y*y * fp(5.5 11 53) + x / (y*fp(2 11 53));
	
	assert(r >= fp(0 11 53));
}