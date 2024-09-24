// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:isolate_paths} NoDuplicateErrors()
{
  var x: int;
  if (*) {
    x := 3;
  }
  else {
    x := 2;
  }
  assert x == 1;
}