// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0, 2} count: int;

procedure {:atomic} {:layer 2} AtomicInc()
modifies count;
{
    count := count + 1;
}
procedure {:yields} {:layer 1} {:refines "AtomicInc"} Inc() {
    var n: int;
    var success: bool;

    while(true)
    invariant {:yields} {:layer 1} true;
    {
        call n := Read();
        yield;
        call success := CAS(n, n+1);
        if (success) {
            break;
        }
    }
}

procedure {:atomic} {:layer 1} AtomicCAS(prev: int, next: int) returns (status: bool)
modifies count;
{
    if (count == prev) {
        count := next;
        status := true;
    } else {
        status := false;
    }
}
procedure {:yields} {:layer 0} {:refines "AtomicCAS"} CAS(prev: int, next: int) returns (status: bool);

procedure {:atomic} {:layer 1} AtomicRead() returns (val: int)
{
    val := count;
}
procedure {:yields} {:layer 0} {:refines "AtomicRead"} Read() returns (val: int);
