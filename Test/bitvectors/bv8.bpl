// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// This file includes some tests for which Boogie once generated bad Z3 input

procedure foo()
{
  var r: bv3;
  var s: bv6;
  var u: bv15;
  var t: bv24;

  t := t[8: 0] ++ t[10: 0] ++ t[24: 18];
  t := (r ++ s) ++ u;
  t := t[16: 0] ++ t[8: 0];
}

procedure bar()
{
  var a: bv64;
  var b: bv32;
  var c: bv8;

  c := a[8:0];
  c := b[8:0];
}
