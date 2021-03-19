// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F(int): bool;
function G(int, int):bool;

procedure A0()
{
    assume (forall {:inst_at "L"} x: int :: F(x-1));
    assert {:inst_add "L", 1} F(0);
    assert (forall y: int :: {:inst_add "L", y+1} F(y));
}

procedure A1()
{
    assume (exists x: int :: {:inst_add "L", x+1} F(x));
    assert (exists {:inst_at "L"} y: int :: F(y-1));
}

procedure A2()
{
    assume (exists x: int :: {:inst_add "L", x+1} F(x));
    assume (forall {:inst_at "L"} y: int :: !F(y-1));
    assert false;
}

procedure A3()
{
    assume (forall {:inst_at "L"} x0: int, {:inst_at "L"} x1: int :: G(x0-1, x1-1));
    assert {:inst_add "L", 1} G(0, 0);
    assert (forall y0, y1: int :: {:inst_add "L", y0+1} {:inst_add "L", y1+1} G(y0, y1));
}

procedure A4()
{
    assume (forall {:inst_at "L0"} x0: int, {:inst_at "L1"} x1: int :: G(x0-1, x1-1));
    assert {:inst_add "L0", 1} {:inst_add "L1", 1} G(0, 0);
    assert (forall y0, y1: int :: {:inst_add "L0", y0+1} {:inst_add "L1", y1+1} G(y0, y1));
}

function P(int, int): bool;

procedure B0()
{
    assume (exists x: int :: (forall {:inst_at "A"} y: int :: P(x,y)));
    assert (forall y: int :: {:inst_add "A", y} (exists x: int :: P(x,y)));
}

procedure B1()
{
    assume (exists x: int :: {:inst_add "B", x+1} (forall {:inst_at "A"} y: int :: P(x,y)));
    assert (forall y: int :: {:inst_add "A", y} (exists {:inst_at "B"} x: int :: P(x-1,y)));
}
