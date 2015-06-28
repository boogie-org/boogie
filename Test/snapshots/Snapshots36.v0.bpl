function {:checksum "2"} F() : bool
{
    true
}

procedure {:checksum "0"} P(b: bool);

implementation {:id "P"} {:checksum "1"} P(p: bool)
{
    var l: [int]bool;

    l := (lambda n: int :: F());
    assert l[0];
}
