// RUN: %boogie /prune:1 /proverOpt:SOLVER=noop /proverLog:"%t-@PROC@.smt2" "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t-B.smt2" "%s"

// B is checked after A on the same prover and does not use toInt, so A's reservation must not reach it.

function {:bvbuiltin "bv2int"} toInt(x: bv8): int;
var bv2int: int;

procedure A(b: bv8) { assert toInt(b) >= 0; }

procedure B() { assert bv2int > 5; }
// CHECK-L: (declare-fun bv2int () Int)
