//Translation from Muller_Kahan.c
//Should Verify
//NOTE:  (fp(....)) causes a compiler error!
//FAILS!  Heavily...

procedure main() returns () {
	var x0 : float(11 53);
	var x1 : float(11 53);
	var x2 : float(11 53);
	var i : int;
	
	x0 := fp(11 11 53) / fp(2 11 53);
	x1 := fp(61 11 53) / fp(11 11 53);
	i := 0;
	while (i < 100) {
		x2 := fp(1130 11 53) - fp(3000 11 53) / x0;
		x2 := fp(111 11 53) - x2 / x1;
		x0 := x1;
		x1 := x2;
		i := i + 1;
	}
	
	assert(x0 >= fp(99 11 53) && x0 <= fp(101 11 53));
}