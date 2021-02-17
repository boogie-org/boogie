function F(int): bool;

procedure A()
{
    assume (forall {:inst_at "L"} x: int :: F(x));
    assert {:inst "L", 0} F(0);
    assert {:inst "L", 0} F(0);
    assert (forall y: int :: {:inst "L", y+1} F(y+1));
}

procedure B(j: int)
requires j > 0;
{
    var x: [int]bool;
    x := (lambda {:inst_at "M"} i: int :: if (i < j) then true else false);
    assert {:inst "M", 0} x[0];
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
    assert {:inst "M", 0} x[0];
}
