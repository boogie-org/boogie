procedure {:checksum "0"} M();

implementation {:id "M"} {:checksum "1"} M()
{
    var x: int;

    x := 0;
    while (*)
    {
        while (*)
        {
            assert true;

            call N();

            call N();

            x := x + 1;

            assert x == 1;  // error
        }

        call N();

        assert false;  // error
    }

    assert true;
}

procedure {:checksum "3"} N();
  ensures true;
