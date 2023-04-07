// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;

pure procedure C()
modifies x;
{
    var c: int;
    c := x;
}

pure procedure D();
requires x > 0;
ensures x < 0;
