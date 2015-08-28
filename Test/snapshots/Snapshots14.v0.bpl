procedure {:checksum "0"} M();

implementation {:id "M"} {:checksum "1"} M()
{
    call N();

    assert false;
}

procedure {:checksum "2"} N();
  ensures F() && G();

function {:checksum "3"} F() : bool
{
    true
}

function {:checksum "4"} G() : bool
{
    false
}
