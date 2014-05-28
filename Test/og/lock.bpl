// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:phase 2} b: bool;

procedure {:yields} {:phase 2} main()
{
    yield;
    while (*)
    {
        yield;

        async call Customer();

        yield;
    }
}

procedure {:yields} {:phase 2} Customer()
{
    yield;
    while (*) 
    {
    	yield;

        call Enter();

    	yield;

    	call Leave();

        yield;
    }
}

procedure {:yields} {:phase 1,2} Enter() 
ensures {:atomic} |{ A: assume !b; b := true; return true; }|;
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

procedure {:yields} {:phase 0,2} CAS(prev: bool, next: bool) returns (status: bool);
ensures {:atomic} |{ 
A: goto B, C; 
B: assume b == prev; b := next; status := true; return true; 
C: status := false; return true; 
}|;

procedure {:yields} {:phase 0,2} Leave();
ensures {:atomic} |{ A: b := false; return true; }|;
