// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} g:int;

action {:layer 1} F(d: int)
{
    var c: int;
    g := c;
}
