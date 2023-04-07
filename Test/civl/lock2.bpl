// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} b: int;

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

action {:layer 2} AtomicEnter()
modifies b;
{ assume b == 0; b := 1; }

yield procedure {:layer 1} Enter()
refines AtomicEnter;
{
    var _old, curr: int;

    while (true)
    invariant {:yields} true;
    {
        call _old := CAS(0, 1);
        if (_old == 0) {
            break;
        }
        while (true)
        invariant {:yields} true;
        {
            call curr := Read();
            if (curr == 0) {
                break;
            }
        }
    }
}

action {:layer 1,2} AtomicRead() returns (val: int)
{ val := b; }

yield procedure {:layer 0} Read() returns (val: int);
refines AtomicRead;

action {:layer 1,2} AtomicCAS(prev: int, next: int) returns (_old: int)
modifies b;
{
  _old := b;
  if (_old == prev) {
    b := next;
  }
}

yield procedure {:layer 0} CAS(prev: int, next: int) returns (_old: int);
refines AtomicCAS;

action {:layer 1,2} AtomicLeave()
modifies b;
{ b := 0; }

yield procedure {:layer 0} Leave();
refines AtomicLeave;

yield procedure {:layer 2} Yield();
