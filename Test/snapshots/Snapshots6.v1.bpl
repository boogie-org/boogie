var x: int;
var y: int;

procedure {:checksum "0"} M();
  modifies x, y;

implementation {:checksum "1"} M()
{
    y := 0;

    call N();

    assert y == 0;
}

procedure {:checksum "3"} N();
  modifies x, y;
