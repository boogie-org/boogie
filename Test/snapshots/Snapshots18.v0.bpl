procedure {:checksum "0"} M();

implementation {:id "M"} {:checksum "1"} M()
{
    while (true)
    {
        assert 0 == 0;
        
        call N();
        call N();

        if (*)
        {
            break;
        }

        assert 1 != 1;
    }

    assert 2 != 2;
}

procedure {:checksum "2"} N();
  ensures false;
