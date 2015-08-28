// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure P0()
{
  var x: int where 0 <= x;
  var y: int where x <= y;

  assert 0 <= x;
  assert x <= y;
  assert y < 5;  // error
}

procedure P1()
{
  var x: int where 0 <= x;
  var y: int where x <= y;

  x := 5;
  havoc y;
  assert 5 <= y;

  havoc x;
  assert 0 <= x;
  assert x <= y;  // error
}

procedure P2()
{
  var x: int where 0 <= x;
  var y: int where x <= y;

  havoc y;  // y first
  havoc x;
  assert x <= y;  // error
}

procedure P3()
{
  var x: int where 0 <= x;
  var y: int where x <= y;

  x := 5;
  havoc x;  // this time, x first
  havoc y;
  assert x <= y;  // yeah!
  assert 5 <= y;  // error
}

procedure P4()
{
  var x: int where 0 <= x;
  var y: int where x <= y;

  havoc x, y;  // both at the same time
  assert 0 <= x && x <= y;
  havoc y, x;  // or in the other order
  assert 0 <= x && x <= y;

  assert x == 7;  // error
}

procedure R0() returns (wProc: int where wProc == xProc,
                        xProc: int where 0 <= xProc,
                        yProc: int where xProc <= yProc);
implementation R0() returns (w: int, x: int, y: int)
{
  while (*) {
    assert w == x;
    assert 0 <= x;
    assert x <= y;
  }
  while (*) {
    assert w == x;
    assert 0 <= x;
    assert x <= y;
    // the following makes w, x, y loop targets
    w := w + 1;
    havoc x;
    y := w;
  }
  assert w == x;
  assert 0 <= x;
  assert x <= y;
}

procedure R1()
{
  var a: int;
  var b: int;
  var c: int;

  call a, b, c := R0();
  assert a == b;
  assert 0 <= b;
  assert b <= c;
}

procedure R2()
{
  var w: int where w == x;
  var x: int where 0 <= x;
  var y: int where x <= y;

  x := 5;
  y := 10;
  while (*) {
    w := w + 1;
    assert w == 6;
    y := y + 2;
    assert 7 <= y;
  }
  assert x == 5 && 0 <= y - w;
  assert y == 10;  // error
}

procedure R3()
{
  var w: int where w == x;
  var x: int where 0 <= x;
  var y: int where x <= y;

  // change w and x
  y := 10;
  while (*) {
    w := w;  x := x;
  }
  assert w == x;
  assert 0 <= x;
  assert y == 10;
  assert w <= 10;  // error
}

procedure R4()
{
  var w: int where w == x;
  var x: int where 0 <= x;
  var y: int where x <= y;

  // change x and y
  w := 12;
  while (*) {
    x := x;  y := y;
  }
  assert 0 <= x;
  assert x <= y;
  assert w == 12;
  assert 8 <= y;  // error
}

procedure R5(K: int)
{
  var w: int where w == x;
  var x: int where 0 <= x;
  var y: int where x <= y;

  // change w and y
  x := K;
  while (*) {
    w := w;  y := y;
  }
  assert w == K;
  assert K <= y;
  assert x == K;
  assert 0 <= x;  // error
}
