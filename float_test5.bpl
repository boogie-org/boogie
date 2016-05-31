//Translation from filter1.c
//Should Verify

function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_INT(int) returns (float64);
function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_REAL(real) returns (float64);

procedure main() returns () {
	var E0 : float64;
	var E1 : float64;
	var S : float64);
	var i : int;
	var rand : int;
	
	E1 := TO_FLOAT64_INT(0);
	S := TO_FLOAT64_INT(0);
	
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