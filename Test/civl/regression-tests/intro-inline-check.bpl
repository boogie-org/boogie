// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 1} g: int;

atomic action {:layer 1} A()
modifies g;
{
    call I();
}

action {:layer 1} I()
modifies g;
{
    g := g  + 1;
}
