// RUN: %boogie -proverLog:%t "%s"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: (set-option :smt.random_seed 100)
// CHECK-L: (set-option :smt.random_seed 0)
procedure {:random_seed 100} WithRandomSeed()
{
}
procedure WithoutRandomSeed()
{
}
