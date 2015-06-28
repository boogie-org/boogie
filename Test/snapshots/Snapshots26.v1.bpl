procedure {:checksum "0"} M();

implementation {:id "M"} {:checksum "2"} M()
{
    var x: int;

    while (*)
    {
        x := 0;
        x := x + 1;
    }

    assert 0 == 0;
    assert x != x;
}
