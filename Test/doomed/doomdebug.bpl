procedure badtrace(x:int, y:int, z:int)
{
  var xin : int;
  xin := x+z;

  
  if (y>5) {
	xin:=5;
  } else {
	assert xin != x;
  }
}

procedure baddiamond(x:int, y:int, z:int)
{
	var xin : int;
	var yin : int;
	var zin : int;
	xin := x;
	yin := y;
	zin := z;
	
	if (y<5) {
		xin := xin -3;		
	} else {
		zin := zin +10;
		xin := 0;
	}
	
	if (x<100) {
		yin := 3;		
	} else {
		zin := 5;
	}
	
	if (z>5) {
		yin := yin - 2;
		xin := xin + 3;
	}

	zin:=zin+yin;
	
	assert xin!=x;	
}
