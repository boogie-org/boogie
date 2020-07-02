// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:yield_invariant} {:layer 1} Yield();

procedure {:yields} {:layer 1} foo()
{
    par A() | B();
    yield;
    par A() | bar();
    yield;
    par bar() | B();
}

procedure {:yields} {:layer 1} bar();

procedure {:yields} {:layer 1} baz1()
{
    par B() | A();
}

procedure {:yields} {:layer 1} baz2()
{
    par A() | C();
}

procedure {:atomic} {:layer 1,1} atomic_A()
{
}
procedure {:yields} {:layer 0} {:refines "atomic_A"} A();

procedure {:left} {:layer 1,1} atomic_B()
{
}
procedure {:yields} {:layer 0} {:refines "atomic_B"} B();

procedure {:right} {:layer 1,1} atomic_C()
{
}
procedure {:yields} {:layer 0} {:refines "atomic_C"} C();
