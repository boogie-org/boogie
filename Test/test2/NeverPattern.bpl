function {:never_pattern true} f1(x:int) returns(int);
function {:never_pattern false} f2(x:int) returns(int);
function f3(x:int) returns(int);


procedure foo()
{
  assume (forall x : int :: f1(x) > 0 && f2(x) > 0 && f3(x) > 0);
  assert f2(3) > 0;
  assert f3(4) > 0;
}

procedure bar()
{
  assume (forall x : int :: f1(x) > 0 && f2(x) > 0 && f3(x) > 0 && f1(7) == 3);
  assert f1(3) > 0;
}

procedure bar1()
{
  assume (forall x : int :: {:nopats f2(x)} f1(x) > 0 && f2(x) > 0 && f3(x) > 0 && f1(7) == 3);
  assert f1(3) > 0;
}

procedure bar2()
{
  assume (forall x : int :: {:nopats f2(x)} f1(x) > 0 && f2(x) > 0 && f3(x) > 0 && f1(7) == 3);
  assert f2(3) > 0;
}
