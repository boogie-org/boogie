// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:phase 1} x:int;

procedure {:yields} {:phase 1} p() 
requires {:phase 1} x >= 5; 
ensures {:phase 1} x >= 8; 
{ 
    yield;
    assert {:phase 1} x >= 5; 
    call Incr(1); 
    yield;
    assert {:phase 1} x >= 6; 
    call Incr(1); 
    yield;
    assert {:phase 1} x >= 7;
    call Incr(1); 
}

procedure {:yields} {:phase 1} q() 
{ 
    call Incr(3); 
}

procedure {:yields} {:phase 0,1} Incr(val: int);
ensures {:atomic}
|{A:
  x := x + val; return true;
}|;
