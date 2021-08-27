// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:identity} Lit<T>(x: T) : T;
axiom Lit(true);

procedure test()
{
    assert Lit(true);
}
