// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type A _;

function f<T>(x: T) : bool;
function g<T>(x: T) : int;

axiom (forall <T> x : A T :: g(x) > 0 ==> f(x));

procedure p() {
    var x: A int;
    assume g(x) > 0;
    assert f(x);
}
