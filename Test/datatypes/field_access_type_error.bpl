// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type T;

procedure A(a: int);
requires a->f == 0;
requires a is T;


procedure B(a: T);
requires a->f == 0;
requires a is T;


datatype Perm {
  Left(i: int), Right(i: int)
}

procedure C(a: Perm);
requires a->f == 0;
requires a is Middle;

procedure D(a: Perm);
requires a->i == 0;

var g: int;

procedure E(x: Perm)
{
    Left(g) := x;
}

procedure F(x: int)
modifies g;
{
    Left(g) := x;
}

datatype Pair { Pair(a: int, b: int) }


procedure G(p: Pair) returns (a: int)
{
  Pair(a, a) := p;
}

procedure H(p: Pair) returns (a: int)
{
  Pair(a, g) := p;
}

procedure I(p: Pair, a: int)
{
  var b: int;
  Pair(a, b) := p;
}

procedure J(p: Pair, x: bool) returns (q: Pair)
{
  q := p->(a := x);
}
