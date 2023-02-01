// RUN: %boogie /proverOpt:C:"-T:1" /proverOpt:BATCH_MODE=true /trace "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: .*solver resource count: -1, 1 proof obligation\]  error
// CHECK-L: z3-hard-timeout.bpl(11,3): Error: this assertion could not be proved

function {:bvbuiltin "bvmul"}  BV256_MULT(x:bv256, y:bv256) returns  (bv256);
function {:bvbuiltin "bvugt"}  BV256_UGT(x:bv256, y:bv256)   returns  (bool);
procedure FactorPrime(a: bv256, b: bv256) {
  assume BV256_UGT(a, 1bv256);
  assume BV256_UGT(b, 1bv256);
  assert BV256_MULT(a,b) != 6189700192562690137449562111bv256;
}
