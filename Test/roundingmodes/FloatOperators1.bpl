// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "fp.add"} ADD(rmode, float24e8, float24e8) returns (float24e8);

procedure foo()
{
  var a : float24e8;
  var b : float24e8;
  var c : float24e8;
  var d : float24e8;

  a := 0e127f24e8;
  b := 0e127f24e8;
  c := ADD(RNA, a, b);
  d := ADD(RTP, a, b);
}
