// RUN: %boogie -inline:spec -print:- -env:0 -printInlined -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var glb:int;

procedure recursivetest()
modifies glb;
{
	glb := 5;
	call glb := recursive(glb);

	return;

}

procedure {:inline 3} recursive(x:int) returns (y:int) 
{

	var k: int;	

	if(x == 0) {
		y := 1;
		return;
	}

	call k := recursive(x-1);
	y := y + k;
	return;

}