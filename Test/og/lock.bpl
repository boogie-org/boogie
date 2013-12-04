var b: bool;

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
}

procedure {:yields} Enter() 
ensures {:atomic} {:phase 0} |{ A: assume !b; b := true; return true; }|;
{
    var status: bool;
    L: 
        yield;
        call status := CAS(false, true);
        goto A, B;

    A: 
        assume status;
	yield;
	return;

    B:
        assume !status;
	goto L;
}

procedure CAS(prev: bool, next: bool) returns (status: bool);
ensures {:atomic} |{ 
A: goto B, C; 
B: assume b == prev; b := next; status := true; return true; 
C: status := false; return true; 
}|;

procedure {:yields} Leave();
ensures {:atomic} |{ A: b := false; return true; }|;
