// RUN: %boogie -typeEncoding:m -proverLog:"%t.smt2" "%s"
// RUN: %OutputCheck "%s" --file-to-check="%t.smt2"
procedure foo() {
  // . is an illegal starting character in SMT-LIBv2
  // so test that we don't emit it as a symbol name.
  // CHECK-L:(declare-fun q@.x () Int)
  var .x:int;
  assert .x == 0;
}
