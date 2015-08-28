// RUN: %boogie -infer:j -instrumentInfer:e -printInstrumented -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure foo () returns ()
{
  var i: int;
  var j: int;
  var n: int;

A:  // true
  n := 0;
  goto B;

B:  // n = 0
  j := 0;
  goto C;

C:  // n = 0 AND j = 0
  i := j + 1;
  goto D;

D:  // n = 0 AND j = 0 AND i = j + 1
  i := i + 1;
  goto E;

E:  // n = 0 AND j = 0 AND i = j + 2
  i := i + 1;
  goto F;

F:  // n = 0 AND j = 0 AND i = j + 3
  i := i + 1;
  goto G;

G:  // n = 0 AND j = 0 AND i = j + 4
  i := i + 1;
  goto H;

H:  // n = 0 AND j = 0 AND i = j + 1
  j := j + 1;
  goto I;

I:  // n = 0 AND j = 1 AND i = j + 4
  return;
}
