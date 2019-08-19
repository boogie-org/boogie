// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// inlining with n=0

var x : int;

procedure {:inline 0} f() // Should not be checked on its own
    modifies x;
{
    x := x + 1;
}

procedure g()
    modifies x;
{
    call f();
}
