// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield invariant {:layer 1} Yield();

yield procedure {:layer 1} foo()
{
    par A() | L();
    call Yield();
    par A() | bar();
    call Yield();
    par bar() | L();
}

yield procedure {:layer 1} bar();

yield procedure {:layer 1} baz1()
{
    par L() | A();
}

yield procedure {:layer 1} baz2()
{
    par A() | R();
}

action {:layer 1,1} atomic_A()
{
}
yield procedure {:layer 0} A() refines atomic_A;

<- action {:layer 1,1} atomic_L()
{
}
yield procedure {:layer 0} L() refines atomic_L;

-> action {:layer 1,1} atomic_R()
{
}
yield procedure {:layer 0} R() refines atomic_R;
