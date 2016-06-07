// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type C;

procedure P(x:int, y:bool) returns (z:C);
procedure Q<a>(x:int, y:a) returns (z:a);

procedure CallP() {
  var x:int;
  var y:bool;
  var z:C;

  call z := P(x, y);
}

procedure CallQ() {
  var x:int;
  var y:bool;
  var z:bool;

  call x := Q(x, y);   // type error
}