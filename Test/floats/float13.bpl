// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_INT(int) returns (float24e8);
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_REAL(real) returns (float24e8);
function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_INT(int) returns (float53e11);
function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_REAL(real) returns (float53e11);

procedure main() returns () {
	var f : float24e8;
	var fc : float24e8;
	var d : float53e11;
	var dc : float53e11;
	
	f := 2097152e129f24e8;
	fc := TO_FLOAT32_INT(5);
	assert(f == fc);
	
	f := -0e126f24e8;
	fc := TO_FLOAT32_REAL(-0.5);
	assert(f == fc);
	
	f := 1048576e128f24e8;
	fc := TO_FLOAT32_REAL(2.25);
	assert(f == fc);
	
	d := 1125899906842624e1025f53e11;
	dc := TO_FLOAT64_INT(5);
	assert(d == dc);
	
	d := 562949953421312e1024f53e11;
	dc := TO_FLOAT64_REAL(2.25);
	assert(d == dc);
}