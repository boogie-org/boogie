procedure P(x: int) returns (y: int);

procedure CallP()
{
  call forall P(5);  // P is allowed here, even if it has out parameters
}

var global: bool;

procedure Q(x: int);
  modifies global;

procedure CallQ()
{
  call forall Q(5);  // error: P is not allowed here, because it has a modifies clause
}

procedure R(x: int);

procedure CallR()
{
  call forall R(5);  // no problem that R has no body, though
}
