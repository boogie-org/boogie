// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "fp.abs RNA"} ABS(float24e8) returns (float24e8);
function {:builtin "fp.leq"} LEQ(rmode, float24e8, float24e8) returns (bool);

procedure foo()
{
  var r : rmode;
  var a : float24e8;
  var b : float24e8;

  a := 0e127f24e8;
  b := 0e127f24e8;

  a := ABS(a);

  if (LEQ(RNA, a, b)) {
    a := b;
  }
}
