// RUN: %boogie -noinfer -typeEncoding:m "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type TT;

procedure A()
{
  var M : [int]bool;
  var N : [int,int]bool;
  var Z : [int,bool]TT;
  var t : TT;


  M[10] := true;
  M[20] := false;
  N[10,20] := true;
  N[10,21] := false;
  N[11,20] := false;

  assert M[10];
  assert !M[20];

  assert N[10,20];
  assert !N[11,20];
  assert !N[10,21];

  assert Z[10,true] == t;
}
