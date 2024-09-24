// RUN: %parallel-boogie "%s" /printSplit:%t /errorTrace:0 > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %diff %S/isolatePaths.bpl.split0.expect %t-NoDuplicateErrors-0.spl
// RUN: %diff %S/isolatePaths.bpl.split1.expect %t-NoDuplicateErrors-1.spl

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