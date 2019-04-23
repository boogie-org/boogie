// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure main() returns () {

  var a : float2e1;
  var b : float1e2;
  var c : float2e2;

  var f : float24e8;
  var d : float53e11;

  a := 0x0.0e0f2e1; //Error
  b := 0x0.0e0f1e2; //Error
  c := 0x0.0e0f2e2; //No Error
  
  f := 0x0.000004e-32f24e8; //Error
  f := 0x0.000008e-32f24e8; //No Error
  f := 0x1.0e32f24e8; //Error
  f := 0x0.8e32f24e8; //No Error
  
  f := 0x1.ffffffe0f24e8; //Error
  f := -0x1.ffffffe0f24e8; //Error
  f := 0x0.ffffffe0f24e8; //No Error
  
  d := 0x0.0000000000002e-256f53e11; //Error
  d := 0x0.0000000000004e-256f53e11; //No Error
  d := 0x1.0e256f53e11; //Error
  d := 0x0.8e256f53e11; //No Error
  
  d := 0x3.fffffffffffffe0f53e11; //Error
  d := -0x3.fffffffffffffe0f53e11; //Error
  d := 0x1.fffffffffffffe0f53e11; //No Error
}
