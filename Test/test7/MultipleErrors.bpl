procedure P(x: int)
{
start:
  goto A, B;

A:
  assert 0 <= x;
  goto C;

B:
  assert x < 100;
  goto C;

C:
  assert x == 87;
  return;
}
