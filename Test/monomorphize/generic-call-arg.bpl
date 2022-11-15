// RUN: %parallel-boogie -lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// A call to a polymorphic function (in an attribute) whose type arguments cannot be resolved
// must be detected and reported as error

procedure B()
{
    assume {:add_to_pool "A", MapConst(false)} true;
}
