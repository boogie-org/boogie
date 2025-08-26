// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x: int;

left action {:layer 1} A_Foo()
{ x := x + 1; }

yield procedure {:layer 0} Foo();
refines A_Foo;

yield left procedure {:layer 1} Bar1()
{
    async call {:sync} Foo();
}

yield left procedure {:layer 1} Bar2()
{
    call Foo();
}

left action {:layer 1} A_Foo2()
{ call A_Foo(); }

yield procedure {:layer 0} Foo2();
refines A_Foo2;

yield left procedure {:layer 1} Baz1()
{
    async call {:sync} Foo2();
}

yield left procedure {:layer 1} Baz2()
{
    call Foo2();
}
