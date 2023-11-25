// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;

pure action E()
modifies x;
{
    var c: int;
    c := x;
}

async atomic action A()
{
}

pure action F()
creates A;
{
}