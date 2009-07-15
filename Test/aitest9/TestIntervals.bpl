procedure P()
{
  var a: int, b: int, c: int;

  a := 0;
  while (*) {
    a := a + 1;
  }
  // a in [0, infty]

  b := 0;
  if (*) { b := b + 1; }
  if (*) { b := b + 1; }
  if (*) { b := b + 1; }
  // b in [0, 3]

  c := a - b;
  // c in [-3, infty]
  goto Next;

  Next:
  assert -3 <= c;
  assert c <= 0;  // error (there was once an error in the Intervals which thought this assertion to be true)
}
