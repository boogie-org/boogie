procedure {:checksum "0"} M();

implementation {:id "M"} {:checksum "1"} M()
{
    assert true;

    call N();

    assert true;

    call N();

    assert false;
}

procedure {:checksum "2"} N();
  ensures false;
