//Translation from filter2.c
//Should give an error
//Same as the previous one; it works with reals!

procedure main() returns () {
	var E : real;
	var E0 : real;
	var E1 : real;
	var S : real;
	var S0 : real;
	var S1 : real;
	var i: int;
	
	havoc E;
	havoc E0;
	assume(E >= 0.0 && E <= 1.0);
	assume(E0 >= 0.0 && E0 <= 1.0);
	
	S0 := 0.0;
	S := 0.0;
	
	i := 0;
	while (i <= 1000000)
	{
		E1 := E0;
		E0 := E;
		
		havoc E;
		assume(E >= 0.0 && E <= 1.0);
		
		S1 := S0;
		S0 := S;
		S := E*0.7 - E0*1.3 + E1*1.1 + S0*1.4 - S1*0.7;
		
		assert(S >= -4.0 && S <= 4.0);
		i := i + 1;
	}
}