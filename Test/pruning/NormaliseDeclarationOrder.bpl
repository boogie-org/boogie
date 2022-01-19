// RUN: %parallel-boogie -infer:j /proverLog:"%t.log" /normalizeDeclarationOrder:1 /proverOpt:SOLVER=noop "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t.log" "%s"
// CHECK-L: (assert (<= N 3))
// CHECK-L: (assert (<= 3 N))

const N: int;
axiom 3 <= N;
axiom N <= 3;

procedure nEquals3()
ensures true;
{
}
