// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} b: bool;

yield procedure {:layer 2} main()
{
    while (*)
    {
        async call Customer();
    }
}

yield procedure {:layer 2} Customer()
{
    while (*)
    invariant {:yields} true;
    {
        call Enter();
        call Yield();
        call Leave();
    }
}

atomic action {:layer 2} AtomicEnter()
modifies b;
{ assume !b; b := true; }

yield procedure {:layer 1} Enter()
refines AtomicEnter;
{
    var status: bool;

    while (true)
    invariant {:yields} true;
    {
        call status := CAS(false, true);
        if (status) {
            return;
        }
    }
}

atomic action {:layer 1,2} AtomicCAS(prev: bool, next: bool) returns (status: bool)
modifies b;
{
  if (b == prev) {
    b := next;
    status := true;
  } else {
    status := false;
  }
}

yield procedure {:layer 0} CAS(prev: bool, next: bool) returns (status: bool);
refines AtomicCAS;

atomic action {:layer 1,2} AtomicLeave()
modifies b;
{ b := false; }

yield procedure {:layer 0} Leave();
refines AtomicLeave;

yield procedure {:layer 2} Yield();
