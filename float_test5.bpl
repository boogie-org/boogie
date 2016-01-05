//Translation from filter1.c
//Should Verify

procedure main() returns () {
	var E0 : float(11 53);
	var E1 : float(11 53);
	var S : float(11 53);
	var i : int;
	var rand : int;
	
	E1 := fp(0 11 53);
	S := fp(0 11 53);
	
	i := 0;
	while (i <= 1000000)
	{
		havoc E0;
		assume(E0 >= fp(-1 11 53) && E0 <= fp(1 11 53));
		
		havoc rand;
		if (rand != 0) {
			S := fp(0 11 53);
		}
		else {
			S := fp(0.999 11 53) * S + E0 - E1;
		}
		E1 := E0;
		
		//assert(1==0);
		assert(S >= fp(-1 11 53) && S <= fp(1 11 53));
		i := i + 1;
	}
}