// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type fl = float24e8;
type float = fl;
type do = float53e11;
type double = do;


procedure foo(x : double) returns (r : float)
{
	r := 0e128f24e8;
	r := 1e127f24e8;
	r := x; //Error
	r := x * 1e127f24e8; //Error
	r := x + 1e127f24e8; //Error
	r := 0e127f24e8 + 0e127f24e8;
	assert(r == 0e128f24e8);
	
	return;
}