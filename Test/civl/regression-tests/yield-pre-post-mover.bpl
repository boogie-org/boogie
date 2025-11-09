// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} g: int;

yield left procedure {:layer 2} A()
requires {:layer 1} g > 0;
preserves {:layer 1} g > 0;
ensures {:layer 1} g > 0;
requires {:layer 1,2} g > 0;
preserves {:layer 1,2} g > 0;
ensures {:layer 1,2} g > 0;
requires {:layer 2} g > 0;
preserves {:layer 2} g > 0;
ensures {:layer 2} g > 0;
{}
