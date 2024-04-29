// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 1} g: int;
var {:layer 0} h: int;
action {:layer 1} A()
modifies g;
{
    call I();
}

action {:layer 1} I()
modifies g;
{
    var x: int;
    g := 1;
    x := h;
}

action {:layer 1,2} B()
modifies g;
{
    call I();
}
