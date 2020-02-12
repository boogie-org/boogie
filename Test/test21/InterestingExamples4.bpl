// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"
// a property that should hold according to the Boogie semantics
// (but no automatic theorem prover will be able to prove it)


type C a;

function sameType<a,b>(x:a, y:b) returns (bool);

axiom (forall<a,b> x:a, y:b :: sameType(x,y) == (exists z:a :: y==z));

// Will be defined to hold whenever the type of y (i.e., b)
// can be reached from the type of x (a) by applying the type
// constructor C a finite number of times. In order words,
// b = C^n(a)
function rel<a,b>(x:a, y:b) returns (bool);

function relHelp<a,b>(x:a, y:b, z:int) returns (bool);

axiom (forall<a, b> x:a, y:b :: relHelp(x, y, 0) == sameType(x, y));
axiom (forall<a, b> n:int, x:a, y:b ::
 (n >= 0 ==>
   relHelp(x, y, n+1) ==
   (exists<c> z:c, y' : C c :: relHelp(x, z, n) && y==y')));

axiom (forall<a, b> x:a, y:b ::
 rel(x, y) == (exists n:int :: n >= 0 && relHelp(x, y, n)));

// Assert that from every type we can reach a type that is
// minimal, i.e., that cannot be reached by applying C to some
// other type. This will only hold in well-founded type
// hierarchies

procedure P() returns () {
  var v : C int;

  assert relHelp(7, 13, 0);
  assert rel(7, 13);

  assert (forall<b> y:b :: (exists<a> x:a ::               // too hard for a theorem prover
   rel(x, y) &&
   (forall<c> z:c :: (rel(z, x) ==> sameType(z, x)))));
}
