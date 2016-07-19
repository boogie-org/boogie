// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo() returns (r : float32) {
	r := 0NaN8e24;
	r := 0nan8e24;
	r := 0+oo8e24;
	r := 0-oo8e24;
	
	return;
}