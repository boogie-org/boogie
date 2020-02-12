// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


type List _;

function NIL<a>() returns (List a);
function Cons<a>(a, List a) returns (List a);

function car<a>(List a) returns (a);
function cdr<a>(List a) returns (List a);

axiom (forall<a> x:a, l:List a :: car(Cons(x, l)) == x);
axiom (forall<a> x:a, l:List a :: cdr(Cons(x, l)) == l);

axiom (forall<a> x:a, l:List a :: Cons(x, l) != NIL());

var l:List bool;

var m:List int;
var mar:[int](List int);

procedure P() returns ()
      requires m != NIL();
      requires mar[0] == m && (forall i:int :: i > 0 ==> mar[i] == cdr(mar[i-1]));
      modifies l, m, mar; {

  l := Cons(true, NIL());

  assert l != NIL();
  l := cdr(l);

  assert l == NIL();
  l := Cons(true, l);
  l := Cons(false, l);

  assert car(mar[1]) == car(cdr(m));
  mar[0] := NIL();
  assert mar[0] != m;

  assert !car(l) && car(cdr(l));
  l := cdr(cdr(l));

  assert (forall i:int :: i > 0 ==> mar[i] == cdr(mar[i-1]));    // error
}

procedure Q() returns () {
  assert Cons(NIL(), NIL()) != NIL();  // warning, but provable
}