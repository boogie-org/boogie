// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo(x : float24e8) returns (r : float24e8)
{
	r := 0e128f24e8;
	r := 1e127f24e8;
	r := x;
	r := x + 1e127f24e8;
	r := 0e127f24e8 + 0e127f24e8;
	assert(r == 0e128f24e8);
	
	return;
}