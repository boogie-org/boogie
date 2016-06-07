// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var{:layer 20} x:int;

procedure{:yields}{:layer 20,25} p_gt1_lower();
  ensures{:both}
  |{
    A:
    x := x + 1;
    return true;
  }|;

procedure{:yields}{:layer 25,40} p_gt1()
  ensures{:both}
  |{
    A:
    x := x + 1;
    return true;
  }|;
{
  yield;
  call p_gt1_lower();
  yield;
}

procedure{:yields}{:layer 20,40} p_gt2();
  ensures{:both}
  |{
    A:
    assert x == 0;
    return true;
  }|;


