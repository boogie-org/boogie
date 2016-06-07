function {:checksum "4"} PlusOne(n: int) : int
{
    n + 2
}

function {:checksum "0"} F(n: int) : int;

axiom (forall n: int :: { F(n) } F(n) == PlusOne(n));

procedure {:checksum "2"} M();

implementation {:id "M"} {:checksum "3"} M()
{
    assert F(0) == 1;  // error
}
