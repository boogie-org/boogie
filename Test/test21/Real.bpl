axiom (forall r: real :: r == 0.0 || r / r == 1.0);

procedure P(a: real, b: real) returns () {
  assume a >= b && a != 0.0 && a >= 1.3579;

  assert 2e0 * (a + 3.0) - 0.5 >= b;
  assert 2e0 * (a + 3.0) - 0.5 > b;
  assert b <= 2e0 * (a + 3.0) - 0.5;
  assert b < 2e0 * (a + 3.0) - 0.5;

  assert 1/2 <= 0.65;
  assert a > 100e-2 ==> 1 / a <= a;
  assert a / 2 != a || a == 0.00;
  assert a != 0.0 ==> a / a == 1.0;

  assert int(a) >= 0 ==> real(3) * a > a;
}