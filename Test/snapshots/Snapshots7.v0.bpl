var x: int;
var y: int;
var z: int;

procedure {:checksum "0"} M();
  modifies x, y, z;

implementation {:id "M"} {:checksum "1"} M()
{
    z := 0;

    call N();

    assert y < 0;
}

procedure {:checksum "2"} N();
  modifies x, y;
  ensures y < z;
