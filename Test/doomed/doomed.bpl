// RUN: %boogie -vc:doomed %s
procedure evilrequires(x:int)
  requires x>0;
{
  var y : int;

  if(x<0) {
    y := 1;
  } else {
    y := 2;
  }
}


procedure evilbranch(x:int)
{
  var y : int;

  if(x<0) {
    y := 1;
  } else {
    y := 2;
  }
  assume y!=2;
  
  assert x<0; 
}


procedure evilloop(x:int)
{
  var y : int;
  y:=x;
  while (y<100) {
     y := y -1;
  }
}

procedure evilnested(x:int)
{
	 var i : int;
	 var j : int;
	 i:=x-1;
	 j:=1;
	 while (i>=0) {
		while (j<=i) {
			assert j<x;
			j := j+1;
		}
		i := i - 1;
	 }
}


procedure evilpath(x:int)
{
  var y : int;
  y:=0;
  if (x>10) {
    y:=3;
  } else {
    assert y!=0;
  }
}

procedure evilcondition(x:int)
{
  var y : int;
  y:=0;
  if (x!=0) {
    y:=3;
  } else {
    assert x!=0;
  }
}

procedure evilensures(x:int) returns  ($result: int)
  ensures $result>0;
{
  var y : int;

  if(x<0) {
    y := 1;
  } else {
    $result:=-1;
  }
}
