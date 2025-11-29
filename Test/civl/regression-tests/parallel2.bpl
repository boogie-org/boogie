// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} a:[int]int;

yield procedure {:layer 1} Allocate() returns ({:linear} tid: One int);

atomic action {:layer 1} AtomicWrite(idx: One int, val: int)
modifies a;
{ a[idx->val] := val; }

yield procedure {:layer 0} Write(idx: One int, val: int);
refines AtomicWrite;

yield procedure {:layer 1} main()
{
    var i: One int;
    var j: One int;
    call i := Allocate();
    call j := Allocate();
    call i := t(i) | j := t(j);
    call i := u(i) | j := u(j);
}

yield procedure {:layer 1} t({:linear_in} i': One int) returns ({:linear} i: One int)
{
    i := i';

    call Write(i, 42);
    call Yield(i, a);
    assert {:layer 1} a[i->val] == 42;
}

yield procedure {:layer 1} u({:linear_in} i': One int) returns ({:linear} i: One int)
ensures call Yield_42(i, 42);
{
    i := i';

    call Write(i, 42);
}

yield invariant {:layer 1} Yield({:linear} i: One int, old_a: [int]int);
preserves old_a[i->val] == a[i->val];

yield invariant {:layer 1} Yield_42({:linear} i: One int, v: int);
preserves v == a[i->val];
