procedure {:checksum "0"} M(n: int);
  requires 0 < n;

implementation {:id "M"} {:checksum "1"} M(n: int)
{
    var x: int;

    call x := N(n);

    assert 0 <= x;
}

procedure {:checksum "2"} N(n: int) returns (r: int);
  requires 0 < n;
  ensures 0 < r;
