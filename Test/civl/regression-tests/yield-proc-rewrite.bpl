// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 1} Foo1({:linear_in} x: Lset int) returns ({:layer 1} z: Lset int)
{
    var y: Lval int;
    z := x;
    call {:layer 1} Lval_Split(z, y);
}

atomic action {:layer 2} AtomicFoo2({:linear_in} x: Lset int) returns (z: Lset int)
{
    var y: Lval int;
    z := x;
    call Lval_Split(z, y);
}
yield procedure {:layer 1} Foo2({:linear_in} x: Lset int) returns ({:layer 1} z: Lset int)
refines AtomicFoo2;
{
    var y: Lval int;
    z := x;
    call {:layer 1} Lval_Split(z, y);
}
