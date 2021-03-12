// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F(int): bool;

procedure A0()
{
    assume (forall {:inst_at "L"} x: int :: F(x-1));
    assert {:inst_add"L", 1} F(0);
    assert (forall y: int :: {:inst_add"L", y+1} F(y));
}

procedure A1()
{
    assume (exists x: int :: {:inst_add"L", x+1} F(x));
    assert (exists {:inst_at "L"} y: int :: F(y-1));
}

procedure A2()
{
    assume (exists x: int :: {:inst_add"L", x+1} F(x));
    assume (forall {:inst_at "L"} y: int :: !F(y-1));
    assert false;
}

procedure B(j: int)
requires j > 0;
{
    var x: [int]bool;
    x := (lambda {:inst_at "M"} i: int :: if (i < j) then true else false);
    assert {:inst_add"M", 0} x[0];
}

procedure C(j: int)
requires j > 0;
{
    var x: [int]bool;
    call x := CreateLambda(j);
    call LookupLambda(x);
}

procedure {:inline 1} CreateLambda(j: int) returns (x: [int]bool)
{
    x := (lambda {:inst_at "M"} i: int :: if (i < j) then true else false);
}

procedure {:inline 1} LookupLambda(x: [int]bool)
{
    assert {:inst_add"M", 0} x[0];
}

function P(int, int): bool;

procedure D0()
{
    assume (exists x: int :: (forall {:inst_at "A"} y: int :: P(x,y)));
    assert (forall y: int :: {:inst_add"A", y} (exists x: int :: P(x,y)));
}

procedure D1()
{
    assume (exists x: int :: {:inst_add"B", x+1} (forall {:inst_at "A"} y: int :: P(x,y)));
    assert (forall y: int :: {:inst_add"A", y} (exists {:inst_at "B"} x: int :: P(x-1,y)));
}
