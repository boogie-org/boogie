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





