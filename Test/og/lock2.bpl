var {:qed} b: int;

procedure {:yields} {:entrypoint} main()
{
    while (*)
    {
        async call Customer();
    }
}

procedure {:yields} {:stable} Customer()
{
    while (*) 
    {
    	yield;

        call Enter();

    	yield;

    	call Leave();
    }

    yield;
}

procedure {:yields} Enter() 
ensures {:atomic 1} |{ A: assume b == 0; b := 1; return true; }|;
{
    var _old, curr: int;
    while (true) { 
    	yield;
        call _old := CAS(0, 1);
	yield;
        if (_old == 0) {
	    return;
	}
	while (true) {
	    yield;
	    call curr := Read();
	    yield;
	    if (curr == 0) {
	        break;
	    }
	}
    }
}

procedure {:yields} Read() returns (val: int);
ensures {:atomic 0} |{ A: val := b; return true; }|;

procedure {:yields} CAS(prev: int, next: int) returns (_old: int);
ensures {:atomic 0} |{ 
A: _old := b; goto B, C; 
B: assume _old == prev; b := next; return true; 
C: assume _old != prev; return true; 
}|;

procedure {:yields} Leave();
ensures {:atomic 0} |{ A: b := 0; return true; }|;
