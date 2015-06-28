// RUN: %boogie -inline:spec -print:- -env:0 -printInlined -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var glb:int;

procedure calculate()
modifies glb;
{
	var x:int;
	var y:int;
	
	y := 5;

	call x := increase(y);
	
	return;
}


procedure {:inline 1} increase (i:int) returns (k:int)
modifies glb;
{
	var j:int;
	
	j := i;
	j := j + 1;
	
	glb := glb + j;

	k := j;

	return;
}
