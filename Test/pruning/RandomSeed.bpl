// RUN: %parallel-boogie -infer:j /proverLog:"%t.log" /normalizeDeclarationOrder:0 /randomSeed:10000 "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t.log" "%s"
// CHECK-L: (assert (<= N 3))
// CHECK-L: (assert (<= 3 N))
// CHECK-L: (set-option :smt.random_seed 136216624)
// CHECK-L: (set-option :sat.random_seed 136216624)
// CHECK-L: random681238191

const N: int;
axiom 3 <= N;
axiom N <= 3;

procedure nEquals3()
ensures true;
{
}
