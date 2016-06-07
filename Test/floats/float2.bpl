// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo(x : float16) returns(r : float32) {
	var y : float64;
	var z : float128;
	
	r := x; // Error
	r := y; // Error
	r := z; // Error
	y := x; // Error
	y := z; // Error
	z := x; // Error

	return;
}