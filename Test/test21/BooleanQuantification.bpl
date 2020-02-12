// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"



function f(bool) returns (int);

axiom f(true) == 17;
axiom f(false) == 19;

procedure P() returns () {
  assert (forall x:bool :: f(x) >= 0);
}

procedure Q() returns () {
  assert (forall x:int :: (x==7 || x==9) ==> x >= 0);
}

procedure R() returns () {
  assert f((forall x:bool :: f(x) >= 10)) < 19;
  assert (exists x:bool :: f(x) > 20);       // should not be provable
}


function g<a>(a) returns (int);

axiom g(true) == 17;
axiom g(false) == 21;

procedure S() returns () {
  assert (forall x:bool :: g(x) >= 0);
  assert g((forall x:bool :: g(x) >= 0)) >= 17;
  assert (forall x:bool :: f(x) == g(x));   // should not be provable
}