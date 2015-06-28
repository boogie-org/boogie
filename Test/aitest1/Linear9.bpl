// RUN: %boogie -infer:j -instrumentInfer:e -printInstrumented -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo () returns ()
{
  var i: int;
  var j: int;
  var n: int;
entry:
  assume n >= 4;
  i := 0;
  j := i + 1;
  // n >= 4 AND i = 0 AND j = i+1
  goto exit, loop0;

loop0:
  // n >= 4 AND i >= 0 AND j = i+1
  assume j <= n;
  goto loop1;
loop1:
  // n >= 4 AND i >= 0 AND j = i+1 AND j <= n
  i := i + 1;
  goto loop2;
loop2:
  j := j + 1;
  // n >= 4 AND i >= 1 AND j = i+1 AND j <= n+1
  goto loop0, exit;

exit:
  // n >= 4 AND i >= 0 AND j = i+1 AND j <= n+1
  return;
}
