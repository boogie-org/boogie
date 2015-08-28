// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const a:bool;
const b:bool;
const c:bool;
const d:bool;

function f(int) returns (bool);
axiom (forall x:int :: f(x) <== x >= 0);

procedure P() {
  assert (a ==> (b ==> c) ==> d) == (d <== (c <== b) <== a);
  assert (a ==> b ==> c) == (c <== (a ==> b));     // error

  assert f(23);
  assert f(-5);                                    // error
}

procedure Q0(x: int) {
  assert x == 2;  // error
  assert x == 2;  // nothing reported for this line, since control cannot reach here
}

procedure Q1(x: int) {
  assert {:subsumption 0} x == 2;  // error
  assert x == 2;  // error (because the subsumption attribute above makes the execution 'forget' the condition)
}

procedure Q2(x: int) {
  assert x == 2;  // error
  assert {:subsumption 0} x == 2;  // nothing reported for this line, since control cannot reach here
}

procedure Q3(x: int) {
  assert {:subsumption 0} x == 2;  // error
  assert {:subsumption 0} x == 2;  // error (because the subsumption attribute above makes the execution 'forget' the condition)
}
