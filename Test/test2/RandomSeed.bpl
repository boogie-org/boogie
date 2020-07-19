// RUN: %boogie -proverLog:%t "%s"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: (set-option :smt.random_seed 100)
procedure {:random_seed 100} TestTimeouts0()
{
}
