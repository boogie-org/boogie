//Translation from addsub_float_exact.c
//Should Verify

function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_INT(int) returns (float32);
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_REAL(real) returns (float32);

procedure main() returns () {
	var x : float32;
	var y : float32;
	var z : float32;
	var r : float32;
	x := TO_FLOAT32_REAL(1e7);
	y := x + TO_FLOAT32_INT(1);
	z := x - TO_FLOAT32_INT(1);
	r := y - z;
	assert r == TO_FLOAT32_INT(2);
}