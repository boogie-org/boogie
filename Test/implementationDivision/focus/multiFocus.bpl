// RUN: %parallel-boogie /printSplit:%t /vcsSplitOnEveryAssert /errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure GuardWithoutFocus(x: int) returns (r: int) 
  ensures r > 0;
{
  if (x > 0) {
     assert x > 2;
     r := 3;
     return;
  }
  
  r := 2;
}

procedure GuardWithFocus(x: int) returns (r: int) 
  ensures r > 0;
{
  if (x > 0) {
     assert {:focus} x > 2;
     r := 3;
     return;
  }
  
  r := 2;
  return;
}

procedure SubSequentAndNestedFocus(x: int)
{
  if (*) {
    if (*) {
      assume {:focus} true;
      assert x > 1;
    } else {
      assert x > 2;
    }
  } else if (*) {
    assume {:focus} true;
    assert x > 3;
  } else {
    assert x > 4;
  }
  assert x > 5;
  if (*) {
    assume {:focus} true;
    assert x > 6;
  } else {
    assert x > 7;
  }
}

procedure {:vcs_split_on_every_assert} EarlyReturn(x: int) {
  if (*) {
    assume {:focus} true;
    assert x > 1;
    return;
  }
  
  assert x > 2;
  assert x > 3;
  assert x > 4;
}