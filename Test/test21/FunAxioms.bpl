// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


type Pair a b;

function MP<a,b>(x:a, y:b) returns (Pair a b);
function Left<a,b>(Pair a b) returns (a);
function Right<a,b>(Pair a b) returns (b);

axiom (forall<a,b> x:a, y:b :: Left(MP(x,y)) == x);
axiom (forall<a,b> x:a, y:b :: Right(MP(x,y)) == y);

type A, B;

procedure P() returns () {

  var x:A, y:B, z:A, p : Pair A B;

  assert Left(MP(x,y)) == x;
  assert Right(MP(x,y)) == y;
  assert Right(MP(x,MP(x,y))) == MP(x,y);
  assert Left(MP(x,MP(x,y))) == x;
  assert Right(Right(MP(x,MP(x,y)))) == y;

  p := MP(x, y);

  p := MP(Left(p), y);

  assert Left(p) == x && Right(p) == y;

  assert Left(p) == z;            // should not be provable

}

procedure Q() returns () {

  assert Left(MP(1,3)) == 1;
  assert Right(MP(1,3)) == 3;
  assert Right(MP(1,true)) == true;

}