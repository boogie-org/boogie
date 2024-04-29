// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Ref;
type Field _;

function foo<T>(f: Field T) : bool;

procedure equality_boogie_poly_paper() {
    var age: Field int;
    var isMarried: Field bool;
    var fInt: Field int;
    var fBool: Field bool;

    /* inspired by example from Leino and Ruemmer in
     * "A Polymorphic Intermediate Verification Language: Design and Logical Encoding" (TACAS 2010)
     */
    assume (forall <T> f: Field T :: (foo(f) || (f == age) || (f == isMarried)));

    assert foo(fInt) || (fInt == age);
    assert foo(fBool) || (fBool == isMarried);
}
