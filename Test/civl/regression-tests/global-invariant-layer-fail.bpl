// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 1,2} x: int;

invariant {:layer 1} Inv1();
preserves x > 0;

invariant {:layer 3} Inv2();
preserves x < 10;