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
  requires x>0;
{
  var y : int;

  if(x<0) {
    y := 1;
  } else {
    y := 2;
  }
}



procedure c(x:int)
  requires x>0;
{
  var y : int;

  if(x<0) {
    y := 1;
    assert false;
  } else {
    y := 2;
  }
}

procedure d(x:int)
  requires x>0;
{
  var y : int;

  if(x<0) {
    assert false;
    y := 1;
  } else {
    y := 2;
  }
}


procedure doomed1(x:int)
{
  var y : int;
  y := 0;
  if(x<0) {
    y := 1;
  } else {
    assert y!=0;
  }
}


procedure doomed2(x:int)
{
  var y : int;
  y := 0;
  if(x!=0) {
    y := 1;
  } else {
    assert x!=0;    
  }
}




