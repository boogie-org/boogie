const N: int;
axiom 0 <= N;

procedure P(K: int)
  requires 0 <= K;
{
  var b: bool, x, k: int;

  if (!b) {
    b := !b;
  }
  x := if b then 13 else 10;
  k := K;
  while (k != 0) {
    x := x + k;
    k := k - 1;
  }
  assert 13 <= x;
}

procedure Thresholds0()
{
  var i: int;
  i := 0;
  while (i < 200)
  {
    i := i + 1;
  }
  assert i == 200;
}

procedure Thresholds1()
{
  var i: int;
  i := 0;
  while (i <= 199)
  {
    i := i + 1;
  }
  assert i == 200;
}

procedure Thresholds2()
{
  var i: int;
  i := 100;
  while (0 < i)
  {
    i := i - 1;
  }
  assert i == 0;
}

procedure Thresholds3()
{
  var i: int;
  i := 0;
  while (i < 200)
  {
    i := i + 1;
  }
  assert i == 199;  // error
}

procedure Thresholds4()
{
  var i: int;
  i := 0;
  while (i + 3 < 203)
  {
    i := i + 1;
  }
  assert i * 2 == 400;  // error: this would hold in an execution, but /infer:j is too weak to infer invariant i<=200
}

