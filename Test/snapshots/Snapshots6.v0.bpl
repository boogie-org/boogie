var x: int;
var y: int;

procedure {:checksum "0"} M();
  modifies x, y;

implementation {:id "M"} {:checksum "1"} M()
{
    y := 0;

    call N();

    assert y == 0;
}

procedure {:checksum "2"} N();
  modifies x;
