// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo() returns (r : float8e24) {
	var d : float53e11;

	r := 0NaN8e24;
	r := 0nan8e24;
	r := 0+oo8e24;
	r := 0-oo8e24;
	r := -5e255f8e24;
	
	d := 0NaN53e11;
	d := 0nan53e11;
	d := 0+oo53e11;
	d := 0-oo53e11;
	d := -200e2000f53e11;
	
	return;
}