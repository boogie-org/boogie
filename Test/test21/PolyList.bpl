// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"



type List a;

function Cons<a>(x:a, y:List a) returns (List a);

// we need some argument ... ugly
function Nil<a>(a) returns (List a);

function Car<a>(List a) returns (a);
function Cdr<a>(List a) returns (List a);

axiom (forall<a> x:a, y:List a :: Car(Cons(x, y)) == x);
axiom (forall<a> x:a, y:List a :: Cdr(Cons(x, y)) == y);

function Len<a>(List a) returns (int);

axiom (forall <a> x:a :: Len(Nil(x)) == 0);
axiom (forall <a> x:a, y:List a :: Len(Cons(x, y)) == 1 + Len(y));



procedure P<a>(param : a) returns () {
  var x:a, NIL : List a, l : List a;

  NIL := Nil(x);

  assert Len(NIL) == 0;
  assert Len(Cons(x,Cons(x,NIL))) == 2;

  l := Cons(x,Cons(x,NIL));
  assert Len(l) == 2;

  l := Cons(x, l);
  assert Len(l) == 3 && Car(l) == x && Len(Cdr(l)) < Len(l);
  assert (forall m : List a, y : a :: Len(Cons(y, m)) > Len(m));

  l := Cdr(l);
  assert Len(l) == 2 && Car(l) == x;

  assert Len(Cons(x,Cons(x,Cons(x,NIL)))) == 2;    // should not be provable

}

procedure Q() returns () {
  var NIL : List int, l : List int;

  NIL := Nil(0);

  assert Len(NIL) == 0;
  assert Len(Cons(1,Cons(2,NIL))) == 2;

  l := NIL;
  l := Cons(42, l);
  l := Cons(Car(l) + 17, Cdr(l));

  assert Len(l) == 1 && Car(l) == 59;

  assert Len(Cons(1,Cons(2,Cons(3,NIL)))) == 2;    // should not be provable

}