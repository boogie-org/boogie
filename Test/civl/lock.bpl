// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} b: bool;

procedure {:yields} {:layer 2} main()
{
    while (*)
    invariant {:cooperates} {:layer 1,2} true;
    {
        async call Customer();
    }
}

procedure {:yields} {:layer 2} Customer()
{
    while (*)
    invariant {:yields} {:layer 1,2} true;
    {
        call Enter();
        yield;
        call Leave();
    }
}

procedure {:atomic} {:layer 2} AtomicEnter()
modifies b;
{ assume !b; b := true; }

procedure {:yields} {:layer 1} {:refines "AtomicEnter"} Enter()
{
    var status: bool;

    while (true)
    invariant {:yields} {:layer 1} true;
    {
        call status := CAS(false, true);
        if (status) {
            return;
        }
    }
}

procedure {:atomic} {:layer 1,2} AtomicCAS(prev: bool, next: bool) returns (status: bool)
modifies b;
{
  if (b == prev) {
    b := next;
    status := true;
  } else {
    status := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicCAS"} CAS(prev: bool, next: bool) returns (status: bool);

procedure {:atomic} {:layer 1,2} AtomicLeave()
modifies b;
{ b := false; }

procedure {:yields} {:layer 0} {:refines "AtomicLeave"} Leave();
