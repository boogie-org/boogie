// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo() returns (r : float32) {
	r := fp<8, 24>(NaN);
	r := fp<8, 24>(+oo);
	r := fp<8, 24>(-oo);
	r := fp<8, 24>(+zero);
	r := fp<8, 24>(-zero);
	
	return;
}