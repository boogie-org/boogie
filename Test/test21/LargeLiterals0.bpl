// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


var x : int;

procedure P() modifies x; {

  x := 1000000;
  assert x > 0 && x < 2000000;

  x := x + 256;
  assert x == 1000256;

  x := 1000000000000;
  x := x + 100100;
  x := x - 100;
  assert x == 1000000100000;

  assert x < -123456789; // error

}