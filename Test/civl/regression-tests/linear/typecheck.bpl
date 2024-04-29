// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type X;

function f(One X): One X;

yield procedure {:layer 1} D()
{
    var {:linear} a: One X;
    var {:linear} x: One X;
    var {:linear} b: Set X;
    var c: One X;
    var {:linear} d: One X;

    b->val[a->val] := true;

    a := c;

    c := a;

    a := d;

    a := a;

    a, x := x, a;

    a, x := x, x;

    call a, x := E(a, x);

    call a, x := E(a, a);

    call a, x := E(a, f(a));

    call a, x := E(a, d);

    call d, x := E(a, x);

    call a, x := E(c, x);

    call c, x := E(a, x);
}

yield procedure {:layer 1} E({:linear_in} a: One X, {:linear_in} b: One X) returns ({:linear} c: One X, {:linear} d: One X)
{
    c := a;
}

var {:linear} g: One int;

procedure G(i:int) returns({:linear} r: One int)
{
  r := g;
}

procedure H(i:int) returns({:linear} r: One int)
modifies g;
{
  g := r;
}

yield procedure {:layer 1} I({:linear_in} x: One int) returns({:linear} x': One int)
{
  x' := x;
}

yield procedure {:layer 1} J()
{
}

yield procedure {:layer 1} P1({:linear_in} x: One int) returns({:linear} x': One int)
{
  par x' := I(x) | J();
  call x' := I(x');
}

yield procedure {:layer 1} P2({:linear_in} x: One int) returns({:linear} x': One int)
{
  call x' := I(x);
  par x' := I(x') | J();
}
