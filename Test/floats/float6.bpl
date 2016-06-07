// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT824_INT(int) returns (float<8, 24>);
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT824_REAL(real) returns (float<8, 24>);
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT824_BV32(bv32) returns (float<8, 24>);
function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT1153_BV64(bv64) returns (float<11, 53>);
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT824_FLOAT32(float32) returns (float<8, 24>);  //Should just be an identity function
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_FLOAT824(float<8, 24>) returns (float32); //Should just be an identity function
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_FLOAT64(float64) returns (float32);
function {:builtin "(_ to_fp 11 53) RNE"} TO_FLOAT64_FLOAT32(float32) returns (float64);

procedure main() returns () {
	var i : int;
	var r : real;
	var f824 : float<8, 24>;
	var f32 : float32;
	var f1153 : float<11, 53>;
	var f64 : float64;
	
	f824 := TO_FLOAT824_INT(5);
	f32 := TO_FLOAT824_INT(5);
	f824 := TO_FLOAT824_REAL(5.0);
	f32 := TO_FLOAT824_REAL(5.0);
	
	f824 := TO_FLOAT824_BV32(0bv32);
	f32 := TO_FLOAT824_BV32(0bv32);
	f1153 := TO_FLOAT1153_BV64(0bv64);
	f64 := TO_FLOAT1153_BV64(0bv64);
	
	f824 := TO_FLOAT824_FLOAT32(fp<8, 24>(0bv32));
	f32 := TO_FLOAT32_FLOAT824(fp<8, 24>(0bv32));
	f824 := TO_FLOAT32_FLOAT64(fp<11, 53>(0bv32));
	f32 := TO_FLOAT32_FLOAT64(fp<11, 53>(0bv32));
	f1153 := TO_FLOAT64_FLOAT32(fp<8, 24>(0bv32));
	f64 := TO_FLOAT64_FLOAT32(fp<8, 24>(0bv32));
	
	f824 := TO_FLOAT824_INT(5);
	f32 := TO_FLOAT32_FLOAT824(f824);
	assert(f32 == f824);
	
	f32 := TO_FLOAT824_INT(5);
	f824 := TO_FLOAT824_FLOAT32(f32);
	assert(f32 == f824);
	
	f32 := TO_FLOAT32_FLOAT64(f64);
	f64 := TO_FLOAT64_FLOAT32(f32);
	
	return;
}