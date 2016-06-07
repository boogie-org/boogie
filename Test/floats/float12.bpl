// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_FLOAT32(float32) returns (float64);
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_FLOAT64(float64) returns (float32);
function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_INT(int) returns (float64);
function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_REAL(real) returns (float64);

procedure main() returns () {
	var x : float64;
	var y : float32;
	
	x := TO_FLOAT64_REAL(1e20)+TO_FLOAT64_INT(1);
	y := TO_FLOAT32_FLOAT64(x);
	assert x != TO_FLOAT64_FLOAT32(y);
}