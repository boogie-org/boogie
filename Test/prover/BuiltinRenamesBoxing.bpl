// RUN: %boogie /typeEncoding:p /proverOpt:SOLVER=noop /proverLog:"%t.smt2" "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t.smt2" "%s"

// bv32_2_U is the function Boogie boxes a bv32 with under /typeEncoding:p. The polymorphic g is what makes it
// box a bv32 at all.

type MyT;
function {:builtin "bv32_2_U"} box(x: bv32): MyT;
function g<a>(x: a): bool;

procedure P(v: bv32, w: MyT)
{
  assume g(v);
  assume box(v) == w;
  assert false;
}
// CHECK-L: (declare-fun bv32_2_U@@0 ((_ BitVec 32)) T@U)
