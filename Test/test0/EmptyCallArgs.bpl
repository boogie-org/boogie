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
  call * := P(*, y);
  call * := P(x, *);
  call z := P(*, *);
  call * := P(*, *);
}

procedure CallQ() {
  var x:int;
  var y:bool;
  var z:bool;

  call z := Q(x, y);
  call * := Q(x, y);
  call z := Q(*, y);
  call z := Q(x, *);
  call * := Q(*, y);
  call * := Q(x, *);  // problem: type parameter cannot be inferred
  call * := Q(*, *);  // problem: type parameter cannot be inferred
}