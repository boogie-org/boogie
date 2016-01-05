//Translation from filter2.c
//Should give an error
//FAILS; doesn't generate terms!

procedure main() returns () {
	var E : float(11 53);
	var E0 : float(11 53);
	var E1 : float(11 53);
	var S : float(11 53);
	var S0 : float(11 53);
	var S1 : float(11 53);
	var i: int;
	
	havoc E;
	havoc E0;
	assume(E >= fp(0.0 11 53) && E <= fp(1.0 11 53));
	assume(E0 >= fp(0.0 11 53) && E0 <= fp(1.0 11 53));
	
	E1 := fp(0.0 11 53);
	S1 := fp(0.0 11 53);
	S0 := fp(0.0 11 53);
	S := fp(0.0 11 53);
	
	i := 0;
//	while (i <= 1000000)
//	{
		E1 := E0;
		E0 := E;
	
		havoc E;
		assume(E >= fp(0.0 11 53) && E <= fp(1.0 11 53));
		
		S1 := S0;
		S0 := S;
		S := E*fp(0.7 11 53) - E0*fp(1.3 11 53) + E1*fp(1.1 11 53) + S0*fp(1.4 11 53) - S1*fp(0.7 11 53);
		
		assert(S >= fp(-4.0 11 53) && S <= fp(4.0 11 53));
		//i := i + 1;
//	}
}