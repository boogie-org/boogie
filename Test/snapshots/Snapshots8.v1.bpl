procedure {:checksum "0"} M(n: int);
  requires 0 < n;

implementation {:id "M"} {:checksum "1"} M(n: int)
{
    var x: int;

    call x := N(n);

    assert 0 <= x;
}

procedure {:checksum "3"} N(n: int) returns (r: int);
  requires 0 < n;
  // Change: stronger postcondition
  ensures 42 < r;
