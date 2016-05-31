//Translation from feedback_diverge.c
//Should give an error
//Not sure on this one...

procedure main() returns () {
	var A : float;
	var B : float;
	var X : float;
	var i : int;
	var rand : int;
	
	A := fp(0);
	B := fp(0);
	
	i := 0;
	while (i < 3600000) {
		
		havoc rand;
		if (rand != 0) {
			havoc X;
			assume(X >= fp(-20) && X <= fp(20));
		}
		else {
			X := B;
		}
		
		B := B - (B * fp(2.0) - A - X) * fp(.005);
		A := X;
		
		i := i + 1;
	}
	
	assert(A >= fp(-100) && A <= fp(100));
}