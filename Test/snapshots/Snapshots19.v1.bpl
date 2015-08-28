procedure {:checksum "0"} M();

implementation {:id "M"} {:checksum "1"} M()
{
    call N();

    assert 1 != 1;
}

procedure {:checksum "3"} N();
  requires 2 == 2;
