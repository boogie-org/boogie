// RUN: %parallel-boogie -quiet -noprune -normalizeNames:0 -proverLog:"%t.noprune.smt2" "%s"
// RUN: %OutputCheck --file-to-check "%t.noprune.smt2" "%s"
// CHECK: ThisIsAFunction

function ThisIsAFunction(): int uses {
  axiom ThisIsAFunction() == 2;
}

procedure P()
{
  assert 1 == 1;
}
