//Translation from inv_square_true-unreach-call.c
//Should Verify

function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_INT(int) returns (float32);
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_REAL(real) returns (float32);

procedure main() returns () {
	var x : float32;
	var y : float32;
	var z : float32;
	
	havoc x;
	assume(x >= TO_FLOAT32_INT(-1) && x <= TO_FLOAT32_INT(1));
	
	if (x <= TO_FLOAT32_REAL(-1e-20) || x >= TO_FLOAT32_REAL(1e-20)) {
		y := x * x;
		assert(y != TO_FLOAT32_INT(0));
		z := TO_FLOAT32_INT(1) / y;
	}
}