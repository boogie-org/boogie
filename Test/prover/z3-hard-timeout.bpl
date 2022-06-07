// RUN: %boogie /proverOpt:C:"-T:1" /proverOpt:BATCH_MODE=true /trace "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: z3-hard-timeout.bpl(8,3): Error: This assertion might not hold.

procedure SquareRoot2NotRational(p: int, q: int)
{
  assume p > 0 && q > 0;
  assert (p * p) !=  2 * (q * q);
}
