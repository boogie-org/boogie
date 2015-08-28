// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo()
{
  var b:bool, i:int;

  b := if i then b else b;
  b := if b then b else i;
  b := if b then i else i;
}
