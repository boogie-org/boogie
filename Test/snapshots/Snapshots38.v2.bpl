procedure {:checksum "-1"} Callee();

implementation {:id "Callee"} {:checksum "2"} Callee()
{
    var r: int;

    call r := Sum(42);
    assert r != 0;
    assert 42 <= r;
}

procedure {:checksum "3"} Sum(n: int) returns (r: int);
  requires 0 <= n;
  ensures n != 0 ==> n <= r;
