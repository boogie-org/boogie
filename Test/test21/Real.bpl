// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"
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

procedure ManyDigitReals()
{
  var x: real;
  var y: real;
  x := 15e-1;
  y := real(3); 
  if (*) {
    assert x == y / 2000000000000000000000000001e-27;  // error
  } else {
    assert x == y / 2000000000000000000000000000e-27;
  }
}

procedure Rounding()
{
  assert real(3) == 3.0;
  assert int(2.2) == int(2.8);
  assert int(2.2) == 2;
  assert int(-2.2) == int(-2.8);
  if (*) {
    assert int(-2.2) == -3;
  } else {
    assert int(-2.2) == -2;  // error: int truncates downward
  }
}

procedure VariousCornerCaseBigDecPrintingTests()
{
  assert 200e-2 == 2.0;
  assert 000e-2 == 0.0;
  assert 000e-1 == 0.0;
  assert 000e-4 == 0.0;
  assert 000e0 == 0.0;
  assert 0e-300 == 0.0;
  assert 12300e-4 == 1.230;
  assert 12300e-5 == 0.123;
  assert 12300e-8 == 000.000123;
  assert 1.9850404e5 == 198504.04;
  assert 19850404e-4 == 1985.0404;
  assert 19850404e-12 == 0.00001985040400000;
  assert 19850404e0000000000000000 == 1985.0404e4;
}
