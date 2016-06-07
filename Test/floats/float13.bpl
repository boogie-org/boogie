// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_INT(int) returns (float64);
function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_REAL(real) returns (float64);

procedure main() returns () {
	var x : float64;
	var y : float64;

	havoc x;
	assume(x >= TO_FLOAT64_INT(0) && x <= TO_FLOAT64_INT(10));

	y := x*x - x;
	if (y >= TO_FLOAT64_INT(0)) {
		y := x / TO_FLOAT64_INT(10);
	}
	else {
		y := x*x + TO_FLOAT64_INT(2);
	}
	
	assert(y >= TO_FLOAT64_INT(0) && y <= TO_FLOAT64_INT(105));
}