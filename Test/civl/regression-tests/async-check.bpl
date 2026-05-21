// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Does not fail async check
yield procedure {:layer 1} A() {
    async call B();
    call X();
}

yield procedure {:layer 1} B() {

}

// Fails async check
yield procedure {:layer 1} C() {
    async call D();
    call X();
}

yield invariant {:layer 1} Foo();
preserves g >= 0;

yield procedure {:layer 1} D() 
requires call Foo();
{
}

var {:layer 0,1} g: int;
both action {:layer 1} A_X()
modifies g;
{
    g := g + 1;
}
yield procedure {:layer 0} X();
refines A_X;
