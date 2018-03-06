// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type float32 = float24e8;

function {:builtin "fp.add"} ADD(rmode, float32, float32) returns (float32);
function {:builtin "fp.eq"} EQ(float32, float32) returns (bool);

procedure {:inline 1} roundingTest(f1: float32, f2: float32)
{
  var rm: rmode;
  var rneSum, rtnSum: float32;

  rm := RNE;
  rneSum := f1 + f2;
  assert EQ(rneSum,1e127f24e8);

  rm := RTN;
  rtnSum := ADD(rm,f1,f2);
  assert EQ(rtnSum,0e127f24e8);
}

procedure Main()
{
  var f1,f2: float32;

  call roundingTest(0e127f24e8, 4194304e103f24e8);

  assume 8388607e126f24e8 < f1 && f1 < 1e127f24e8;
  assume 4194303e103f24e8 < f2 && f2 < 4194305e103f24e8;
  call roundingTest(f1, f2);
}
