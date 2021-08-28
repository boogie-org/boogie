// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:inline} foo<T>(x: T): T {
    x
}

function {:inline} foo'<T>(x: T): T {
    (var y := x; foo(y))
}

function {:inline} bar1<T>(x: T): T {
    foo'(x)
}

function {:inline} bar2<T>(x: T): T {
    foo'(x)
}

procedure A(a: int) returns (a': int)
ensures a' == a;
{
    a' := foo(a);
    a' := foo'(a);
}

procedure B(a: int) returns (a': int)
ensures a' == a;
{
    a' := bar1(a);
    a' := bar2(a');
}

procedure C(a: int) returns (a':int)
ensures a' == a;
{
    a':= bar1(bar2(a));
}

procedure D(a: int) returns (a':int)
ensures a' == a;
{
    a' := a - 1;
    a':= bar1((var x := a'; bar2(a')) + 1);
}

type X;
procedure A'(a: X) returns (a': X)
ensures a' == a;
{
    a' := foo(a);
    a' := foo'(a);
}

procedure B'(a: X) returns (a': X)
ensures a' == a;
{
    a' := bar1(a);
    a' := bar2(a');
}

procedure C'(a: X) returns (a': X)
ensures a' == a;
{
    a':= bar1(bar2(a));
}
