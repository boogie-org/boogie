// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure main() returns () {
	var x : float24e8;
	var y : float24e8;
	var z : float24e8;
	var r : float24e8;
	x := 0e40f24e8;
	y := x + 0e0f24e8;
	z := x - 0e0f24e8;
	r := y - z;
	assert r == 0e1f24e8;
}