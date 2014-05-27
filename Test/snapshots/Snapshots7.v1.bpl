var x: int;
var y: int;
var z: int;

procedure {:checksum "0"} M();
  modifies x, y, z;

implementation {:checksum "1"} M()
{
    z := 0;

    call N();

    assert y < 0;
}

procedure {:checksum "3"} N();
  modifies x;
  ensures y < z;
