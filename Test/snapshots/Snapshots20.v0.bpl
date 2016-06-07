procedure {:checksum "0"} M();

implementation {:id "M"} {:checksum "1"} M()
{
    if (*)
    {
        call N();

        assert 1 != 1;
    }
    else
    {
        assert 2 != 2;  // error
    }

    assert 3 != 3;
}

procedure {:checksum "2"} N();
  ensures 0 != 0;
