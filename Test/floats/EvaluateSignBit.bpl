// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo()
{
  var a : float53e11;
  var b : float53e11;
  var c : float53e11;
  a := 0x3.2e1f53e11; //50.0
  b := 0x1.fd70a3d70a3d7e0f53e11; //1.99
  c := -0x1.fd70a3d70a3d7e0f53e11; //-1.99
  b := (b * a) / a;
  c := (c * a) / a;
  assert (b > 0x0.0e0f53e11); //b should be positive
  assert (c < 0x0.0e0f53e11); //c should be negative
}
