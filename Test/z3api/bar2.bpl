
procedure {:inline 1} foo() returns (x: bool)
{
  var b: bool;
  if (b) {
    x := false;
    return;
  } else {
    x := true;
    return;
  }
}

procedure main()
{
  var b1: bool;
  var b2: bool;

  call b1 := foo();
  call b2 := foo();
  assert b1 == b2;
}


