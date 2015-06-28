// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure {:selective_checking} foo()
{
  var x, y, z : int;

  assert x < y;
  assert y < z;
  assume {:start_checking_here} true;
  assert x < z;
}

procedure {:selective_checking} foo_fail1()
{
  var x, y, z : int;

  assert x < y;
  assume {:start_checking_here} true;
  assert x < z;
}

procedure {:selective_checking} foo_fail2()
{
  var x, y, z : int;

  assert x < y;
  
  if (*) {
    assume {:start_checking_here} true;
  }

  assert x < z;
}

procedure foo_no_selch()
{
  var x, y, z : int;

  assert x < y;
  assume {:start_checking_here} true;
  assert x < z;
}

