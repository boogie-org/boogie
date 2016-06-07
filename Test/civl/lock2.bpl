// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} b: int;

procedure {:yields} {:layer 2} main()
{
    yield;
    while (*)
    {
        async call Customer();
        yield;
    }
    yield;
}

procedure {:yields} {:layer 2} Customer()
{
    yield;
    while (*) 
    {
        call Enter();
    	yield;
    	call Leave();
        yield;
    }
    yield;
}

procedure {:yields} {:layer 1,2} Enter() 
ensures {:atomic} |{ A: assume b == 0; b := 1; return true; }|;
{
    var _old, curr: int;
    yield;
    while (true) { 
        call _old := CAS(0, 1);
	yield;
        if (_old == 0) {
	    break;
	}
	while (true) {
	    call curr := Read();
	    yield;
	    if (curr == 0) {
	        break;
	    }
	}
	yield;
    }
    yield;
}

procedure {:yields} {:layer 0,2} Read() returns (val: int);
ensures {:atomic} |{ A: val := b; return true; }|;

procedure {:yields} {:layer 0,2} CAS(prev: int, next: int) returns (_old: int);
ensures {:atomic} |{ 
A: _old := b; goto B, C; 
B: assume _old == prev; b := next; return true; 
C: assume _old != prev; return true; 
}|;

procedure {:yields} {:layer 0,2} Leave();
ensures {:atomic} |{ A: b := 0; return true; }|;
