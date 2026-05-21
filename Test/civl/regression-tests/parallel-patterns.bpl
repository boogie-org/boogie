// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield invariant {:layer 1} Yield();

yield procedure {:layer 1} foo()
{
    call A() | L();
    call Yield();
    call A() | bar();
    call Yield();
    call bar() | L();
}

yield procedure {:layer 1} bar();

yield procedure {:layer 1} baz1()
{
    call L() | A();
}

yield procedure {:layer 1} baz2()
{
    call A() | R();
}

atomic action {:layer 1,1} atomic_A()
{
}
yield procedure {:layer 0} A();
refines atomic_A;

left action {:layer 1,1} atomic_L()
{
}
yield procedure {:layer 0} L();
refines atomic_L;

right action {:layer 1,1} atomic_R()
{
}
yield procedure {:layer 0} R();
refines atomic_R;
