var {:qed} b: bool;

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
ensures {:atomic 1} |{ A: assume !b; b := true; return true; }|;
{
    var status: bool;
    yield;
    L: 
        call status := CAS(false, true);
	yield;
        goto A, B;

    A: 
        assume status;
	yield;
	return;

    B:
        assume !status;
	goto L;
}

procedure {:yields} CAS(prev: bool, next: bool) returns (status: bool);
ensures {:atomic 0} |{ 
A: goto B, C; 
B: assume b == prev; b := next; status := true; return true; 
C: status := false; return true; 
}|;

procedure {:yields} Leave();
ensures {:atomic 0} |{ A: b := false; return true; }|;
