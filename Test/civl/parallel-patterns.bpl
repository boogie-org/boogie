// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:yield_invariant} {:layer 1} Yield();

procedure {:yields} {:layer 1} foo()
{
    par A() | L();
    yield;
    par A() | bar();
    yield;
    par bar() | L();
}

procedure {:yields} {:layer 1} bar();

procedure {:yields} {:layer 1} baz1()
{
    par L() | A();
}

procedure {:yields} {:layer 1} baz2()
{
    par A() | R();
}

procedure {:atomic} {:layer 1,1} atomic_A()
{
}
procedure {:yields} {:layer 0} {:refines "atomic_A"} A();

procedure {:left} {:layer 1,1} atomic_L()
{
}
procedure {:yields} {:layer 0} {:refines "atomic_L"} L();

procedure {:right} {:layer 1,1} atomic_R()
{
}
procedure {:yields} {:layer 0} {:refines "atomic_R"} R();
