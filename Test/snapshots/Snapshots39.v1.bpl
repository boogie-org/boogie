procedure {:checksum "-1"} Callee();

implementation {:id "Callee"} {:checksum "2"} Callee()
{
    var r: int;

    call r := Sum(42);
    assert r != 0;
    assert r == (42 * 43) div 2;
}

procedure {:checksum "1"} Sum(n: int) returns (r: int);
  requires 0 <= n;
  ensures n <= r;
