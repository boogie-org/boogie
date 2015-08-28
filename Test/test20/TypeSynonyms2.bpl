// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %boogie -noVerify -print:- -pretty:0 -env:0 -printDesugared "%s" > "%t"
// RUN: %diff "%s.print.expect" "%t"


type Set a = [a]bool;

function union<a>(x : Set a, y : Set a) returns (Set a);
axiom (forall<a> x : Set a, y : Set a, z : a :: (x[z] || y[z]) == union(x, y)[z]);


const intSet0 : Set int;
axiom (forall x:int :: intSet0[x] == (x == 0 || x == 2 || x == 3));

const intSet1 : Set int;
axiom (forall x:int :: intSet1[x] == (x == -5 || x == 3));


procedure P() returns () {
  assert (forall x:int :: union(intSet0, intSet1)[x] ==
                                     (x == -5 || x == 0 || x == 2 || x == 3));
}

