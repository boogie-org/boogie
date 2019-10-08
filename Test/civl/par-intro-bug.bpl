// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0} x : int;

procedure {:layer 0} set_x(v: int)
ensures {:layer 0} x == v;	 
modifies x;
{
  x := v;
}	

procedure {:yields} {:layer 0} yield_set_x(v: int)
ensures {:layer 0} x == v;	
{
  yield;
	call set_x(v);
}

procedure {:yields} {:layer 0} main()
{
  par yield_set_x(4) | yield_set_x(3);
	assert {:layer 0} false;
}	
