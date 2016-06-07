// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "(_ to_fp 8 23) RNE"} TO_FLOAT823_INT(int) returns (float<8, 23>);
function {:builtin "(_ to_fp 8 23) RNE"} TO_FLOAT823_REAL(real) returns (float<8, 23>);
function {:builtin "(_ to_fp 8 23) RNE"} TO_FLOAT823_BV31(bv31) returns (float<8, 23>);
function {:builtin "(_ to_fp 8 23) RNE"} TO_FLOAT823_BV32(bv32) returns (float<8, 23>);
function {:builtin "(_ to_fp 8 23) RNE"} TO_FLOAT823_FLOAT824(float<8, 24>) returns (float<8, 23>);
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT824_FLOAT823(float<8, 23>) returns (float<8, 24>);

procedure foo(x : float<8, 24>) returns (r : float<8, 24>) {
	r := TO_FLOAT823_INT(5); // Error
	r := TO_FLOAT823_REAL(5.0); // Error
	r := TO_FLOAT823_BV31(0bv31); // Error
	r := TO_FLOAT823_BV32(0bv32); // Error
	r := TO_FLOAT823_FLOAT824(fp<8, 24>(1bv32)); // Error
	r := TO_FLOAT824_FLOAT823(fp<8, 24>(1bv32)); // Error
	r := TO_FLOAT824_FLOAT823(fp<8, 23>(1bv31));
	
	r := TO_FLOAT823_FLOAT824(x); // Error
	r := TO_FLOAT824_FLOAT823(x); // Error
	
	return;
}