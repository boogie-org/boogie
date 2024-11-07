// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x: int;

yield procedure {:layer 0} A(i: int) returns (j: int);
refines both action {:layer 1} B {
    x := x + 1;
}