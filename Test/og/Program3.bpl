// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:phase 1} x:int;

procedure {:yields} {:phase 1} yield_x()
ensures {:phase 1} x >= old(x); 
{
    yield;
    assert {:phase 1} x >= old(x);
}

procedure {:yields} {:phase 1} p() 
requires {:phase 1} x >= 5; 
ensures {:phase 1} x >= 8; 
{ 
    call yield_x();
    call Incr(1); 
    call yield_x();
    call Incr(1); 
    call yield_x();
    call Incr(1); 
    call yield_x();
}

procedure {:yields} {:phase 1} q() 
{ 
    yield;
    call Incr(3); 
    yield;
}

procedure {:yields} {:phase 0,1} Incr(val: int);
ensures {:atomic}
|{A:
  x := x + val; return true;
}|;
