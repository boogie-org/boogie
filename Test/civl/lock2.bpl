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

procedure {:atomic} {:layer 2} AtomicEnter()
modifies b;
{ assume b == 0; b := 1; }

procedure {:yields} {:layer 1} {:refines "AtomicEnter"} Enter()
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

procedure {:atomic} {:layer 1,2} AtomicRead() returns (val: int)
{ val := b; }

procedure {:yields} {:layer 0} {:refines "AtomicRead"} Read() returns (val: int);

procedure {:atomic} {:layer 1,2} AtomicCAS(prev: int, next: int) returns (_old: int)
modifies b;
{
  _old := b;
  if (_old == prev) {
    b := next;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicCAS"} CAS(prev: int, next: int) returns (_old: int);

procedure {:atomic} {:layer 1,2} AtomicLeave()
modifies b;
{ b := 0; }

procedure {:yields} {:layer 0} {:refines "AtomicLeave"} Leave();