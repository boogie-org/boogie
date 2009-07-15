
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