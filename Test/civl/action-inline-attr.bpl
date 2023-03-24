// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 1, 2} l: int;

link action {:inline} {:layer 1} set_l(v: int)
modifies l;
{
    l := v;
}
