// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo(x : bv32) returns(r : bv32)
{
  var q : bv64;

  block1:
  	r := 17bv32;
	assert r == r;
    assert r[32:0] == r[32:0];
    assert 0bv2 ++ r[12:0] == 0bv2 ++ r[12:0];
    r := 17bv10 ++ 17bv22;
  	// r := 17;
    q := 420000000000bv64;
    q := 8444249301319680000bv64;
    q := 16444249301319680000bv64;
  return;
}

