// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "(_ to_fp 8 23) RNE"} TO_FLOAT823_INT(int) returns (float23e8);
function {:builtin "(_ to_fp 8 23) RNE"} TO_FLOAT823_REAL(real) returns (float23e8);
function {:builtin "(_ to_fp 8 23) RNE"} TO_FLOAT823_BV31(bv31) returns (float23e8);
function {:builtin "(_ to_fp 8 23) RNE"} TO_FLOAT823_BV32(bv32) returns (float23e8);
function {:builtin "(_ to_fp 8 23) RNE"} TO_FLOAT823_FLOAT824(float24e8) returns (float24e8);
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT824_FLOAT823(float23e8) returns (float24e8);

procedure foo(x : float24e8) returns (r : float24e8) {
  r := TO_FLOAT823_INT(5); // Error
  r := TO_FLOAT823_REAL(5.0); // Error
  r := TO_FLOAT823_BV31(0bv31); // Error
  r := TO_FLOAT823_BV32(0bv32); // Error
  r := TO_FLOAT823_FLOAT824(0x0.0e0f24e8); // Error
  r := TO_FLOAT824_FLOAT823(0x0.0e0f23e8); // Error
  
  r := TO_FLOAT823_FLOAT824(x); // Error
  r := TO_FLOAT824_FLOAT823(x); // Error
  
  return;
}
