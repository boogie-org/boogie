// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

atomic action {:layer 2} AtomicFoo() returns (o: int)
{
    var y: int;
    o := y;
}
yield procedure {:layer 1} Foo() returns (o: int) 
refines AtomicFoo;
{
    var x: int;
    o := x;
}