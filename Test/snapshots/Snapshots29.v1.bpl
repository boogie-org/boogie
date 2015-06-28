procedure {:checksum "0"} P();

implementation {:id "P"} {:checksum "2"} P()
{
    var i: int;

    i := 0;

    while (*)
    {
        i := 1;
    }

    assert i == 0;
}
