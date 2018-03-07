// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure foo()
{
  var a : rmode;
  var b : rmode;

  a := RNE;
  b := roundNearestTiesToEven;
  assert (a == b);

  a := RNA;
  b := roundNearestTiesToAway;
  assert (a == b);

  a := RTP;
  b := roundTowardPositive;
  assert (a == b);

  a := RTN;
  b := roundTowardNegative;
  assert (a == b);

  a := RTZ;
  b := roundTowardZero;
  assert (a == b);
}
