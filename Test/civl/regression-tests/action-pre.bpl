// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

invariant {:layer 1} Pre(x: int);
preserves x == 1;

left action {:layer 1} A_Foo(x: int)
requires call Pre(x: int);
{ }

yield procedure {:layer 0} Foo(x: int);
refines A_Foo;

yield procedure {:layer 1} Bar(x: int)
requires {:layer 1} x == 1;
{
    call Foo(x);
} 