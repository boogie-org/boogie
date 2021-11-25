// RUN: %boogie "%s" -normalizeNames:1 -mv:"%t".model > "%t"
// RUN: grep STATE "%t".model >> "%t"
// RUN: %diff "%s.expect" "%t"

procedure Abs(x: int) returns (y: int)
  ensures y >= 0;
{
  assume {:captureState "structure.dfyl(3,0): initial state"} true;  // SHOWS IN MODEL
  goto LabelA, LabelB;

  LabelA:
  assume {:captureState "structure.dfyl(5,2): then branch"} true;
  assume 0 <= x;
  y := x;
  goto Done;

  LabelB:
  assume {:captureState "structure.dfyl(5,2): else branch"} true;  // SHOWS IN MODEL
  assume x < 0;
  y := x;  // error: should be -x
  goto LabelC;

  LabelC:
  assume {:captureState "structure.dfyl(6,2): y is x"} true;  // SHOWS IN MODEL
  y := y + 2;
  y := y + 3;
  assume {:captureState "structure.dfyl(8,2): y is 5 more than x"} true;  // SHOWS IN MODEL
  assume {:captureState "structure.dfyl(9,2): no change to y"} true;  // SHOWS IN MODEL
  y := y - 5;
  goto Done;

  Done:
  assume {:captureState "structure.dfy(10,0): done"} true;  // SHOWS IN MODEL
}

procedure BadCall(x: int) returns (y: int)
{
  var r: int;

  assume {:captureState "structure.dfyl(100,0): initial state"} true;  // SHOWS IN MODEL
  r := 0;
  goto LabelA, LabelB;

  LabelA:
  assume {:captureState "structure.dfyl(101,2): then branch"} true;
  assume x < 50;
  goto Done;

  LabelB:
  assume {:captureState "structure.dfyl(102,2): else branch"} true;  // SHOWS IN MODEL
  assume 0 <= x;
  y := x;
  call r := Callee(y);  // error
  y := 200;
  assume {:captureState "structure.dfyl(103,2): shortly after call"} true;
  goto Done;

  Done:
  assume {:captureState "structure.dfy(110,0): done"} true;
}
procedure Callee(x: int) returns (ret: int);
  requires x < 20;

procedure BadAssert(x: int) returns (y: int)
  requires x <= 10;
{
  assume {:captureState "structure.dfyl(200,0): initial state"} true;  // SHOWS IN MODEL for both errors
  y := x;
  goto LabelA;

  LabelA:
  assume {:captureState "structure.dfyl(201,2): then branch"} true;  // SHOWS IN MODEL for both errors
  assert y < 1000;
  assume {:captureState "structure.dfyl(202,2): then branch"} true;  // SHOWS IN MODEL for both errors
  assert y < 100;
  assume {:captureState "structure.dfyl(203,2): then branch"} true;  // SHOWS IN MODEL for both errors
  assert y < 20;
  assume {:captureState "structure.dfyl(204,2): then branch"} true;  // SHOWS IN MODEL for both errors
  assert y < 8;
  assume {:captureState "structure.dfyl(205,2): then branch"} true;  // SHOWS IN MODEL for second error
  assert y < 12;
  assume {:captureState "structure.dfyl(206,2): then branch"} true;  // SHOWS IN MODEL for second error
  assert y < 9;
  assume {:captureState "structure.dfyl(207,2): then branch"} true;  // SHOWS IN MODEL for second error
  assert y < 4;
}
