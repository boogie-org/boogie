// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 1} foo();
requires call foo();
ensures call foo();
preserves call foo();

atomic action {:layer 1} bar();
requires call bar();