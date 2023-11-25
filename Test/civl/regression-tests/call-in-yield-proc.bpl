// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 1} Foo1({:linear_in} x: Lset int) returns (z: Lset int)
{
    var y: Lval int;
    z := x;
    call {:layer 1} Lval_Split(z, y);
}

var {:layer 0,1} w: Lset int;

yield procedure {:layer 1} Foo2()
{
    var y: Lval int;
    call {:layer 1} Lval_Split(w, y);
}

var {:layer 1,2} a: Lset int;
yield procedure {:layer 2} Foo3()
{
    var y: Lval int;
    call {:layer 1} Lval_Split(a, y);
}
