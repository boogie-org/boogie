// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure foo()
{
  var a : rmode;
  var b : rmode;

  a := RNE;
  b := RNE;

  assert (a == b);
}
