// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "fp.add"} ADD(rmode, float53e11, float53e11) returns (float53e11);
function {:builtin "fp.sub"} SUB(rmode, float53e11, float53e11) returns (float53e11);

procedure foo(a : float53e11, b : float53e11)
{
  var c : float53e11;
  var d : float53e11;
  var e : float53e11;
  var f : float53e11;
  var g : float53e11;

  c := ADD(RTZ, a, b);
  d := ADD(RNE, a, b);
  e := ADD(RNA, a, b);
  f := ADD(RTP, a, b);
  g := ADD(RTN, a, b);
  assert (c == d);
  assert (c == e);
  assert (c == f);
  assert (c == g);

  c := SUB(RTZ, a, b);
  d := SUB(RNE, a, b);
  e := SUB(RNA, a, b);
  f := SUB(RTP, a, b);
  g := SUB(RTN, a, b);
  assert (c == d);
  assert (c == e);
  assert (c == f);
  assert (c == g);
}
