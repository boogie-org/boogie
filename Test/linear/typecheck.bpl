// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X;

procedure A()
{
    var {:linear "A"} a: X;
    var {:linear "A"} b: int;
}

procedure B()
{
    var {:linear "B"} a: X;
    var {:linear "B"} b: [X]bool;
}

procedure C()
{
    var {:linear "C"} a: X;
    var {:linear "C"} c: [X]int;
}

function f(X): X;

procedure {:yields} {:phase 1} D()
{
    var {:linear "D"} a: X;
    var {:linear "D"} x: X;
    var {:linear "D"} b: [X]bool;
    var c: X;
    var {:linear "D2"} d: X;

    b[a] := true;

    a := f(a);

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

    yield;
    par a := F(a) | x := F(a);
    yield;
}

procedure E({:linear "D"} a: X, {:linear "D"} b: X) returns ({:linear "D"} c: X, {:linear "D"} d: X)
{
    c := a;
}

procedure {:yields} {:phase 0} F({:linear "D"} a: X) returns ({:linear "D"} c: X);

var {:linear "x"} g:int;

procedure G(i:int) returns({:linear "x"} r:int)
{
  r := g;
}

procedure H(i:int) returns({:linear "x"} r:int)
modifies g;
{
  g := r;
}

procedure {:yields} {:phase 0} I({:linear ""} x:int) returns({:linear ""} x':int)
{
  x' := x;
}

procedure {:yields} {:phase 0} J()
{
}

procedure {:yields} {:phase 1} P1({:linear ""} x:int) returns({:linear ""} x':int)
{
  yield;
  par x' := I(x) | J();
  yield;
  call x' := I(x');
  yield;
}

procedure {:yields} {:phase 1} P2({:linear ""} x:int) returns({:linear ""} x':int)
{
  yield;
  call x' := I(x);
  yield;
  par x' := I(x') | J();
  yield;
}
