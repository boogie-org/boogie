// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} b: bool;

procedure {:yields} {:layer 2} main()
{
    while (*)
    {
        async call Customer();
    }
}

procedure {:yields} {:layer 2} Customer()
{
    while (*)
    invariant {:yields 1,2} true;
    {
        call Enter();
        par yield_1() | yield_2();
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
    invariant {:yields 1} true;
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

procedure {:yield_invariant} {:layer 1} yield_1();
procedure {:yield_invariant} {:layer 2} yield_2();