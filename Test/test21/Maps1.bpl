

// different map type classes with the same arity

const c : [int] bool;
const d : [ref] bool;
const e : <a> [a] bool;
const f : <a> [a] a;

axiom (c[17] ==> c[19]);
axiom (forall<t> x:t :: e[x]);
axiom (!d[null]);
axiom (forall<t> x:t :: f[x] == x);

procedure P() returns () {

  var x : <a> [a] bool;

  assume !c[19];
  assert !c[17];

  x := e;
  x[true] := false;
  x[17] := true;

  assert !x[true];
  assert !(forall<t> y:t :: x[y]);
  assert x != e;

  assert f[x] == x;
  assert f[17] > 17;      // should not be provable

}

type ref;
const null : ref;
