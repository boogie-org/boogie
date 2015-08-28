var g: int;

procedure {:checksum "0"} P();
  requires g == 0;
  modifies g;

implementation {:id "P"} {:checksum "1"} P()
{
    call Q();
    assert 0 < g;
}

procedure {:checksum "2"} Q();
  modifies g;
  ensures old(g) < g;
