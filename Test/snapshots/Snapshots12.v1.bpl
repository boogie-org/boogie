procedure {:checksum "0"} M();

implementation {:id "M"} {:checksum "1"} M()
{
    call N();

    assert false;
}

procedure {:checksum "2"} N();
  ensures F();

function {:checksum "4"} F() : bool
{
    true
}
