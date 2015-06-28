procedure {:checksum "0"} M();

implementation {:id "M"} {:checksum "1"} M()
{
    var x: int;

    assume x == 0;

    while (*)
    {
    }

    assert 0 == 0;
    assert x == 0;
}
