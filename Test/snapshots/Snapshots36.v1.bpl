function {:checksum "3"} F() : bool
{
    false
}

procedure {:checksum "0"} P(b: bool);

implementation {:id "P"} {:checksum "1"} P(p: bool)
{
    var l: [int]bool;

    l := (lambda n: int :: F());
    assert l[0];
}
