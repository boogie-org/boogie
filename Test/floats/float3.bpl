// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure main() returns () {
	var x : float24e8;
	var y : float24e8;
	var z : float24e8;
	
	z := x + y;
	z := x - y;
	z := x * y;
	assume(y != 0e0f24e8);
	z := x / y;
	
	z := (0e127f24e8 + 0e127f24e8 + 0e0f24e8);
	assert(z == 0e128f24e8);
	
	z := 0e128f24e8 - 0e127f24e8;
	assert(z == 0e127f24e8);
	
	z := 0e127f24e8 * 0e127f24e8;
	assert(z == 0e127f24e8);
	
	z := 0e127f24e8 / 0e127f24e8;
	assert(z == 0e127f24e8);
	
	return;
}