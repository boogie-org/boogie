// RUN: %parallel-boogie "%s" /printSplit:%t /errorTrace:0 > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %diff %S/isolatePaths.bpl.NoDuplicateErrors-0.expect %t-NoDuplicateErrors-0.spl
// RUN: %diff %S/isolatePaths.bpl.NoDuplicateErrors-1.expect %t-NoDuplicateErrors-1.spl
// RUN: %diff %S/isolatePaths.bpl.EarlyAssertions--1.expect %t-EarlyAssertions--1.spl
// RUN: %diff %S/isolatePaths.bpl.EarlyAssertionsVariant-0.expect %t-EarlyAssertionsVariant-0.spl
// RUN: %diff %S/isolatePaths.bpl.EarlyAssertionsVariant-1.expect %t-EarlyAssertionsVariant-1.spl
// RUN: %diff %S/isolatePaths.bpl.EmptyPath--1.expect %t-EmptyPath--1.spl

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

// We expect only a single VC
procedure {:isolate_paths} EmptyPath()
{
  var x: int;
  x := 10;
  if (*) {
    assert x > 5;
  } else {
  }
}

// We expect a single VC that contains both assertions
procedure {:isolate_paths} EarlyAssertions()
{
  var x: int;
  x := 10;
  assert x > 5; // Should only be asserted once
  if (*) {
    assert x > 6;
  } else {
  }
}

// We expect two VCs, one with two assertions
procedure {:isolate_paths} EarlyAssertionsVariant()
{
  var x: int;
  x := 10;
  assert x > 5; // Should only be asserted once
  if (*) {
    assert x > 4;
  } else {
    assert x > 6;
  }
}