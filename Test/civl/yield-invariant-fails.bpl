// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} g: int;

yield invariant {:layer 1} Inv();
invariant g > 0;

procedure {:yields} {:layer 1} foo()
{
    call A();
}

procedure {:yields} {:layer 0} {:refines "atomic_A"} A();
procedure {:atomic} {:layer 1,1} atomic_A()
modifies g;
{
    g := g - 1;
}
