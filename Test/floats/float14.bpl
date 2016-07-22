// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure main() returns () {
	var f : float24e8;
	var d : float53e11;
	
	f := 0e-1f24e8; //Error
	f := 0e256f24e8; //Error
	f := 0e255f24e8; //No Error
	
	f := 8388608e0f24e8; //Error
	f := -8388608e0f24e8; //Error
	f := 8388607e0f24e8; //No Error
	
	d := 0e-1f53e11; //Error
	d := 0e2048f53e11; //Error
	d := 0e2047f53e11; //No Error
	
	d := 4503599627370496e0f53e11; //Error
	d := -4503599627370496e0f53e11; //Error
	d := 4503599627370495e0f53e11; //No Error
}