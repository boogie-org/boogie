procedure {:checksum "-1"} Callee();

implementation {:id "Callee"} {:checksum "0"} Callee()
{
    var r: int;

    call r := Sum(42);
    assert r != 0;
}

procedure {:checksum "1"} Sum(n: int) returns (r: int);
  requires 0 <= n;
  ensures n <= r;
