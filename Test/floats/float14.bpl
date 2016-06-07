// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_INT(int) returns (float64);
function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_REAL(real) returns (float64);

procedure main() returns () {
	var x : float64;
	var y : float64;
	var r : float64;
	
	x := TO_FLOAT64_INT(77617);
	y := TO_FLOAT64_INT(33096);
	r := y*y*y*y*y*y * TO_FLOAT64_REAL(333.75) + x*x * (x*x*y*y*TO_FLOAT64_INT(11) - y*y*y*y*y*y - y*y*y*y * TO_FLOAT64_INT(121) - TO_FLOAT64_INT(2)) + y*y*y*y*y*y*y*y * TO_FLOAT64_REAL(5.5) + x / (y*TO_FLOAT64_INT(2));
	
	assert(r >= TO_FLOAT64_INT(0));
}