//Translation from rlim_exit.c
//Should verify
//Unary - unsupported float operations (on my end)...

procedure main() returns () {
	var X : float;
	var Y : float;
	var S : float;
	var R : float;
	var D : float;
	var i : int;
	
	Y := fp(0);
	
	i := 0;
	while (i < 100000) {
		havoc X;
		havoc D;
		assume(X >= fp(-128) && X <= fp(128));
		assume(D >= fp(0) && D <= fp(16));
		
		S := Y;
		Y := X;
		R := X - S;
		if (R <= fp(0)-D) {
			Y := S - D;
		}
		else if(R >= D) {
			Y := S + D;
		}
		
		i := i + 1;
	}
	
	assert(Y >= fp(-129) && Y <= fp(129));
}