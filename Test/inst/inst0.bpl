function F(int): bool;

procedure A()
{
    assume (forall {:inst_label "L"} x: int :: F(x));
    assert {:inst "L", 0} F(0);
    assert {:inst "L", 0} F(0);
    assert (forall {:inst "L", y+1} y: int :: F(y+1));
}

procedure B()
{
    var x: [int]bool;
    x := (lambda i: int :: true);
}
