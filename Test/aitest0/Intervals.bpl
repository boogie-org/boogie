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
