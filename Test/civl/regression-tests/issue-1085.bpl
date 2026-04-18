// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 1} Foo({:linear_in} x: UnitMap (One int), i: int)
    returns ({:linear} x': UnitMap (One int))
requires {:layer 1} Map_Contains(x, One(i));
refines atomic action _ { x' := x; }
{
    var a: UnitMap (One int);
    var b: One int;

    b := One(i);
    a := x;
    call a, b := Bar(a, i);
    x' := a;
}

yield procedure {:layer 1} Bar({:linear_in} a: UnitMap (One int), i: int)
    returns ({:linear} a': UnitMap (One int), {:linear} b: One int)
requires {:layer 1} Map_Contains(a, One(i));
refines atomic action _ { a' := a; b := One(i); call One_Get(a', b); }
{
    a' := a;
    b := One(i);
    call One_Get(a', b);
}