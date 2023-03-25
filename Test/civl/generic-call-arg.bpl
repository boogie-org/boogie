// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// A call to a polymorphic function (in an attribute) whose type arguments cannot be resolved
// must be detected and reported as error

yield procedure {:layer 1} B();
requires call A(MapConst(false));

yield invariant {:layer 1} A(x: [int]bool);
