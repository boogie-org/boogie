// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo()
{
  var a: [int,int]int;
  var b: [int]bool;
  a := (lambda y:int :: y + 1);
  b := (lambda y:int :: y + 1);
}

procedure bar()
{
  var a: [int]int;
  a := (lambda<T> y:int :: y + 1);
}

procedure baz()
{
  var a: [bool]int;
  a := (lambda y:bool :: y + 1);
}
