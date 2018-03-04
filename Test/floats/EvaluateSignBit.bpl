// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo()
{
  var a : float53e11;
  var b : float53e11;
  var c : float53e11;
  a := 2533274790395904e1028f53e11; //50.0
  b := 3483252836794368e1023f53e11; //1.99
  c := -3483252836794368e1023f53e11; //-1.99
  b := (b * a) / a;
  c := (c * a) / a;
  assert (b > 0e0f53e11); //b should be positive
  assert (c < 0e0f53e11); //c should be negative
}
