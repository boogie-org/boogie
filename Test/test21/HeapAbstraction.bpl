

type Field a, Heap = <a>[ref, Field a]a;

function f<b>(<a>[b, Field a]a) returns (int);

axiom (forall x:<a>[int, Field a]a :: f(x) == 17);

axiom (forall x:<a>[ref, Field a]a :: f(x) == 42);

procedure P() returns () {
  var h : Heap, g : <a>[bool, Field a]a;

  assert f(h) == 42;
  assert f(g) >= 0;     // should not be provable
}

type ref;
const null : ref;
