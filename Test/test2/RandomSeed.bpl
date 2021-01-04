// RUN: %boogie -proverOpt:O:smt.random_seed=55 -proverLog:"%t.smt2" "%s"
// RUN: %OutputCheck --file-to-check "%t.smt2" "%s"
// CHECK-L: (set-info :boogie-vc-id WithRandomSeed0)
// CHECK-L: (set-option :smt.random_seed 100)
// CHECK-L: (set-option :smt.random_seed 55)
// CHECK-L: (set-info :boogie-vc-id WithoutRandomSeed0)
// CHECK-L: (set-info :boogie-vc-id WithRandomSeed1)
// CHECK-L: (set-option :smt.random_seed 99)
// CHECK-L: (set-option :smt.random_seed 55)
// CHECK-L: (set-info :boogie-vc-id WithoutRandomSeed1)
procedure {:random_seed 100} WithRandomSeed0()
{
}
procedure WithoutRandomSeed0()
{
}
procedure {:random_seed 99} WithRandomSeed1()
{
}
procedure WithoutRandomSeed1()
{
}
