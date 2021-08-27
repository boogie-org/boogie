// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// A call to a polymorphic function (in an attribute) whose type arguments cannot be resolved
// must be detected and reported as error

procedure
{:layer 1}
{:yield_requires "A", MapConst(false)}
B();

procedure {:yield_invariant} {:layer 1} A(x: [int]bool);
