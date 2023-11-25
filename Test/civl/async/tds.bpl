// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} Tid = int;

const unique DEFAULT: int;
const unique CREATED: int;
const unique PROCESSED: int;
const unique FINISHED: int;

var status:[int]int;

atomic action {:layer 5} atomic_main({:linear "tid"} id: int, {:linear_in "tid"} tids: [int]bool)
modifies status;
{
    assert id == c;
    assert (forall i: int :: (0 <= i && i < n) <==> tids[i]);
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == DEFAULT);
    status := (lambda j: int :: if (0 <= j && j < n) then FINISHED else status[j]);
}

left action {:layer 4} atomic_server({:linear "tid"} id: int, {:linear_in "tid"} tids: [int]bool)
modifies status;
{
    assert id == c;
    assert (forall i: int :: (0 <= i && i < n) <==> tids[i]);
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == DEFAULT);
    status := (lambda j: int :: if (0 <= j && j < n) then CREATED else status[j]);
}

left action {:layer 4} atomic_client({:linear "tid"} id: int)
modifies status;
{
    assert id == c;
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == CREATED);
    status := (lambda j: int :: if (0 <= j && j < n) then PROCESSED else status[j]);
}

left action {:layer 4} atomic_master({:linear "tid"} id: int)
modifies status;
{
    assert id == c;
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == PROCESSED);
    status := (lambda j: int :: if (0 <= j && j < n) then FINISHED else status[j]);
}

const c: int;
const n: int;
axiom 0 <= n;

yield procedure {:layer 4} main({:linear "tid"} id: int, {:linear_in "tid"} tids: [int]bool)
refines atomic_main;
{
    var i: int;
    var sid: int;
    var mid: int;
    var cid: int;

    call server3(id, tids);
    call client3(id);
    call master3(id);
}

yield procedure {:layer 2} Alloc(i: int, {:linear_in "tid"} tidq: [int]bool) returns ({:linear "tid"} id: int, {:linear "tid"} tidq':[int]bool);
refines AtomicAlloc;
both action {:layer 3} AtomicAlloc(i: int, {:linear_in "tid"} tidq: [int]bool) returns ({:linear "tid"} id: int, {:linear "tid"} tidq':[int]bool)
{ assert tidq[i]; id := i; tidq' := tidq[i := false]; }

yield procedure {:layer 3} server3({:linear "tid"} id: int, {:linear_in "tid"} tids: [int]bool)
refines atomic_server;
{
    var i: int;
    var {:layer 3} snapshot: [int]int;
    var {:linear "tid"} tids': [int]bool;
    var {:linear "tid"} tid: int;

    i := 0;
    call {:layer 3} snapshot := Copy(status);
    tids' := tids;
    while (i < n)
    invariant {:layer 3} 0 <= i && i <= n;
    invariant {:layer 3} (forall j: int :: i <= j && j < n <==> tids'[j]);
    invariant {:layer 3} status == (lambda j: int :: if (0 <= j && j < i) then CREATED else snapshot[j]);
    {
        call tid, tids' := Alloc(i, tids');
        async call {:sync} server2(tid);
        i := i + 1;
    }
}

left action {:layer 3} atomic_server2({:linear "tid"} i: int)
modifies status;
{
    assert status[i] == DEFAULT;
    status[i] := CREATED;
}
yield procedure {:layer 2} server2({:linear "tid"} i: int);
refines atomic_server2;

yield procedure {:layer 3} client3({:linear "tid"} id: int)
refines atomic_client;
{
    call client2();
}

atomic action {:layer 3} atomic_client2()
modifies status;
{
    assume (forall i: int :: 0 <= i && i < n ==> status[i] == CREATED);
    status := (lambda j: int :: if (0 <= j && j < n) then PROCESSED else status[j]);
}
yield procedure {:layer 2} client2();
refines atomic_client2;

yield procedure {:layer 3} master3({:linear "tid"} id: int)
refines atomic_master;
{
    call master2();
}

atomic action {:layer 3} atomic_master2()
modifies status;
{
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == PROCESSED);
    status := (lambda j: int :: if (0 <= j && j < n) then FINISHED else status[j]);
}
yield procedure {:layer 2} master2();
refines atomic_master2;
