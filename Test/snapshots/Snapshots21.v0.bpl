procedure {:checksum "0"} M();

implementation {:id "M"} {:checksum "1"} M()
{
    if (*)
    {
        assert 1 != 1;  // error
    }
    else
    {
        assert 2 != 2;  // error
    }

    assert 3 != 3;
}
