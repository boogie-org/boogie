procedure {:checksum "-1"} Foo(b: bool);

implementation {:id "Foo"} {:checksum "2"} Foo(b: bool)
{
    var r: int;

    assert b;
    call r := Sum(42);
    assert r != 0;
    assert r == (42 * 43) div 2;
}

procedure {:checksum "3"} Sum(n: int) returns (r: int);
  requires 0 <= n;
  ensures r == (n * (n + 1)) div 2;
