// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} g: int;

yield invariant {:layer 1} Inv();
invariant g > 0;

yield procedure {:layer 1} foo()
{
    call A();
}

yield procedure {:layer 0} A();
refines atomic_A;
atomic action {:layer 1,1} atomic_A()
modifies g;
{
    g := g - 1;
}
