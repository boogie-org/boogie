procedure {:checksum "0"} M(x: int);
implementation {:id "M"} {:checksum "1"} M(x: int)
{                     assert x < 20 || 10 <= x;  // always true
  assert x < 10;  // error
  call Other(x);  // error: precondition violation
}

procedure {:checksum "10"} Other(y: int);
  requires 0 <= y;
implementation {:id "Other"} {:checksum "11"} Other(y: int)
{
}

procedure {:checksum "20"} Posty() returns (z: int);
  ensures 2 <= z;  // error: postcondition violation
implementation {:id "Posty"} {:checksum "21"} Posty() returns (z: int)
{
  var t: int;
  t := 20;
  if (t < z) {
  } else {  // the postcondition violation occurs on this 'else' branch
  }
}

procedure {:checksum "30"} NoChangeWhazzoeva(u: int);
implementation {:id "NoChangeWhazzoeva"} {:checksum "3"} NoChangeWhazzoeva(u: int)
{
  assert u != 53;  // error
}

procedure {:checksum "40"} NoChangeAndCorrect();
implementation {:id "NoChangeAndCorrect"} {:checksum "41"} NoChangeAndCorrect()
{
  assert true;
}
