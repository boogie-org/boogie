/*
In functions marked with {:selective_checking} all asserts are turned into assumes,
except for the ones reachable from the commands marked with {:start_checking_here}.
Thus, "assume {:start_checking_here} whatever;" is an inverse of "assume false;".
The first one disables all verification before it, and the second one disables
all verification after.
*/

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

