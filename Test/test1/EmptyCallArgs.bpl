type C;

procedure P(x:int, y:bool) returns (z:C);
procedure Q<a>(x:int, y:a) returns (z:a);

procedure CallP() {
  var x:int;
  var y:bool;
  var z:C;

  call z := P(x, y);
  call * := P(x, y);
  call z := P(*, y);
  call z := P(x, *);
  call * := P(*, x);   // type error
  call * := P(x, *);
  call z := P(*, *);
  call * := P(*, *);
}

procedure CallQ() {
  var x:int;
  var y:bool;
  var z:bool;

  call x := Q(x, y);   // type error
  call * := Q(x, y);
  call x := Q(*, y);   // type error
  call x := Q(x, *);
  call * := Q(*, y);
}