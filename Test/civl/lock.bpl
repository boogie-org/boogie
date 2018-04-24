// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} b: bool;

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

procedure {:atomic} {:layer 2} AtomicEnter()
modifies b;
{ assume !b; b := true; }

procedure {:yields} {:layer 1} {:refines "AtomicEnter"} Enter()
{
    var status: bool;
    yield;
    while (true) {
        call status := CAS(false, true);
        if (status) {
            yield;
            return;
        }
        yield;
    }
    yield;
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
