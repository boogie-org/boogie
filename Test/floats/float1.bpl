// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo(x : float24e8) returns (r : float24e8)
{
	r := 0e1f24e8;
	r := 1e0f24e8;
	r := x;
	r := x + 1e0f24e8;
	r := 0e0f24e8 + 0e0f24e8;
	assert(r == 0e1f24e8);
	
	return;
}