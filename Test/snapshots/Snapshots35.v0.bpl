procedure {:checksum "0"} P(b: bool);
  requires b;

implementation {:id "P"} {:checksum "1"} P(p: bool)
{
    assert p;
}
