// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x: int;
var {:layer 0,2} y: int;

atomic action {:layer 1} A()
modifies x, y;
refines B;
{
    x := x + 1;
    call X();
}

action {:layer 1} X()
modifies y;
{
    y := y + 1;
}

atomic action {:layer 2} B()
modifies x;
{
    havoc x;
}