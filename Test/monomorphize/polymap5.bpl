// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type A _;

function f<T>(x: A T) : bool;
function g<T>(x: A T) : int;

axiom (forall <T> a : A T :: (forall <R> b: A R :: g(a) > g(b) ==> f(a) ==> f(b)));

procedure p() {
    var x: A int;
    var y: A bool;
    assume g(x) > 0;
    assume g(y) < 0;
    assert g(x) > g(y);
    assume f(x);
    assert f(y);
}
