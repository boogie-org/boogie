// RUN: %boogie -vc:doomed %s
procedure a(x:int)
{
  var y : int;

  if(x<0) {
    y := 1;
  } else {
    y := 2;
  }
}


procedure b(x:int)
{
  var y : int;

  if(x<0) {
    y := 1;
  } else {
    y := 2;
    assert false;
  }
}


procedure c(x:int)
{
  var y : int;

  if(x<0) {
    y := 1;
  } else {
    y := 2;
    assert {:PossiblyUnreachable} false;
  }
}

procedure useCE(x:int)
{
  var y : int;

  if(x<0) {
    y := 1;
  } else {
    y := 2;
  }
  if(x<7) {    
    y := 5;
  } else {	
    y := 6;
  }

}




