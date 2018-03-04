// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure foo()
{
  var a : rmode;
  var b : rmode;
  var c : rmode;

  a := RNE;
  b := RNE;

  c := a + b;
  c := a - b;
  c := a * b;
  c := a / b;

  if (a <= b) {
    c := a;
  } else if (a >= b) {
    c := b;
  }

  if (a < b) {
    c := a;
  } else if (a > b) {
    c := b;
  }
}
