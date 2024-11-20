// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x: int;

yield procedure {:layer 0} A(i: int) returns (j: int);
refines both action {:layer 1} _ {
    x := x + 1;
}

yield procedure {:layer 1} B(i: int) returns (j: int)
refines both action {:layer 2} _ {
    x := x + 1;
}
{
    call j := A(i);
}

yield procedure {:layer 0} C(i: int) returns (j: int);
refines both action {:layer 1} AC {
    call Incr();
}

action {:layer 1} Incr()
modifies x;
{
    x := x + 1;
}