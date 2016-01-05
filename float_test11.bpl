//Translation from interpolation.c
//Should Verify
//Returns inconclusize?  What does that mean?

procedure main() returns () {
	var i : int;
	var z : float;
	var t : float;
	var min : [int] float;
	var max : [int] float;
	
	min[0] := fp(5);
	min[1] := fp(10);
	min[2] := fp(12);
	min[3] := fp(30);
	min[4] := fp(150);
	
	max[0] := fp(10);
	max[1] := fp(12);
	max[2] := fp(30);
	max[3] := fp(150);
	max[4] := fp(300);
	
	havoc t;
	assume(t >= min[0] && t <= max[4]);
	
	i := 0;
	while (i < 5) {
		if (t <= max[i]) {
			break;
		}
		i := i + 1;
	}
	
	z := (t - min[i]) / (max[i] - min[i]);
	
	assert(z >= fp(0) && z <= fp(1));
}