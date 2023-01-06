// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F(int): bool;
function G(int, int):bool;

procedure A0()
{
    assume (forall {:pool "L"} x: int :: F(x-1));
    assert {:add_to_pool "L", 1} F(0);
    assert (forall y: int :: {:add_to_pool "L", y+1} F(y));
}

procedure A1()
{
    assume (exists x: int :: {:add_to_pool "L", x+1} F(x));
    assert (exists {:pool "L"} y: int :: F(y-1));
}

procedure A2()
{
    assume (exists x: int :: {:add_to_pool "L", x+1} F(x));
    assume (forall {:pool "L"} y: int :: !F(y-1));
    assert false;
}

procedure A3()
{
    assume (forall {:pool "L"} x0: int, {:pool "L"} x1: int :: G(x0-1, x1-1));
    assert {:add_to_pool "L", 1} G(0, 0);
    assert (forall y0, y1: int :: {:add_to_pool "L", y0+1, y1+1} G(y0, y1));
}

procedure A4()
{
    assume (forall {:pool "L0"} x0: int, {:pool "L1"} x1: int :: G(x0-1, x1-1));
    assert {:add_to_pool "L0", 1} {:add_to_pool "L1", 1} G(0, 0);
    assert (forall y0, y1: int :: {:add_to_pool "L0", y0+1} {:add_to_pool "L1", y1+1} G(y0, y1));
}

procedure A5()
{
    assume (var a := (forall {:pool "L"} x: int :: F(x-1)); a);
    assert {:add_to_pool "L", 1} F(0);
    assert (var b := (forall y: int :: {:add_to_pool "L", y+1} F(y)); b);
}

procedure A6()
{
    assume !(exists {:pool "L"} x: int :: !F(x-1));
    assert {:add_to_pool "L", 1} F(0);
    assert !(exists y: int :: {:add_to_pool "L", y+1} !F(y));
}

procedure A7()
{
    var a: bool;
    assume a ==> (forall {:pool "L"} x: int :: F(x-1));
    assert {:add_to_pool "L", 1} a ==> F(0);
    assert a ==> (forall y: int :: {:add_to_pool "L", y+1} F(y));
}

procedure A8()
{
    var a: bool;
    assume (exists {:pool "L"} x: int :: F(x-1)) ==> a;
    assert {:add_to_pool "L", 1} F(0) ==> a;
    assert (exists y: int :: {:add_to_pool "L", y+1} F(y)) ==> a;
}

function P(int, int): bool;

procedure B0()
{
    assume (exists x: int :: (forall {:pool "A"} y: int :: P(x,y)));
    assert (forall y: int :: {:add_to_pool "A", y} (exists x: int :: P(x,y)));
}

procedure B1()
{
    assume (exists x: int :: {:add_to_pool "B", x+1} (forall {:pool "A"} y: int :: P(x,y)));
    assert (forall y: int :: {:add_to_pool "A", y} (exists {:pool "B"} x: int :: P(x-1,y)));
}
