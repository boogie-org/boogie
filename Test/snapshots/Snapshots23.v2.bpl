procedure {:checksum "0"} M();

implementation {:id "M"} {:checksum "5"} M()
{
    if (*)
    {
        // Don't remove this comment.
        assert 1 != 1;  // error
    }
    else
    {
        assert 2 == 2;
    }
}


procedure {:checksum "2"} N();

implementation {:id "N"} {:checksum "4"} N()
{
    assert 4 == 4;
}
