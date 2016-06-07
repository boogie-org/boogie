// RUN: %boogie -inline:spec -print:- -env:0 -printInlined -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure main(x:int)
{
	var A:[int]int;
	var i:int;
	var b:bool;
	var size:int;
	
	call i,b := find(A, size, x);

	if(b) {
		assert(i > 0 && A[i] == x);
	}

	return;
}

procedure {:inline 1} find(A:[int]int, size:int, x:int) returns (ret:int, found:bool)
{
	var i:int;
	var b:bool;

	ret := -1;
	b := false;
	found := b;
	i := 0;

	while(i < size) {
		call b := check(A, i, x);
		if(b) {
		      ret := i;
		      found := b;
		      break;
		}
	
	}

	return;

}


procedure {:inline 3} check (A:[int]int, i:int, c:int) returns (ret:bool)
	  requires i >= 0;
	  ensures (old(A[i]) > c) ==> ret == true;
{
	if(A[i] == c) {
		ret := true;
	} else {
	       ret := false;
	}
	return;
}