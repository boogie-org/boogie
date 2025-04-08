// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const unique DEFAULT: int;
const unique CREATED: int;
const unique PROCESSED: int;
const unique FINISHED: int;

var status:[int]int;

atomic action {:layer 5} atomic_main({:linear} id: One int, {:linear_in} tids: Set int)
modifies status;
{
    assert id->val == c;
    assert (forall i: int :: (0 <= i && i < n) <==> Set_Contains(tids, i));
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == DEFAULT);
    status := (lambda j: int :: if (0 <= j && j < n) then FINISHED else status[j]);
}

left action {:layer 4} atomic_server({:linear} id: One int, {:linear_in} tids: Set int)
modifies status;
{
    assert id->val == c;
    assert (forall i: int :: (0 <= i && i < n) <==> Set_Contains(tids, i));
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == DEFAULT);
    status := (lambda j: int :: if (0 <= j && j < n) then CREATED else status[j]);
}

left action {:layer 4} atomic_client({:linear} id: One int)
modifies status;
{
    assert id->val == c;
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == CREATED);
    status := (lambda j: int :: if (0 <= j && j < n) then PROCESSED else status[j]);
}

left action {:layer 4} atomic_master({:linear} id: One int)
modifies status;
{
    assert id->val == c;
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == PROCESSED);
    status := (lambda j: int :: if (0 <= j && j < n) then FINISHED else status[j]);
}

const c: int;
const n: int;
axiom 0 <= n;

yield procedure {:layer 4} main({:linear} id: One int, {:linear_in} tids: Set int)
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

yield procedure {:layer 2} Alloc(i: int, {:linear_in} tidq: Set int) returns ({:linear} id: One int, {:linear} tidq': Set int);
refines AtomicAlloc;
both action {:layer 3} AtomicAlloc(i: int, {:linear_in} tidq: Set int) returns ({:linear} id: One int, {:linear} tidq': Set int)
{ id := One(i); tidq' := tidq; call One_Split(tidq', id); }

yield procedure {:layer 3} server3({:linear} id: One int, {:linear_in} tids: Set int)
refines atomic_server;
{
    var i: int;
    var {:layer 3} snapshot: [int]int;
    var {:linear} tids': Set int;
    var {:linear} tid: One int;

    i := 0;
    call {:layer 3} snapshot := Copy(status);
    tids' := tids;
    while (i < n)
    invariant {:layer 3} 0 <= i && i <= n;
    invariant {:layer 3} (forall j: int :: i <= j && j < n <==> Set_Contains(tids', j));
    invariant {:layer 3} status == (lambda j: int :: if (0 <= j && j < i) then CREATED else snapshot[j]);
    {
        call tid, tids' := Alloc(i, tids');
        async call {:sync} server2(tid);
        i := i + 1;
    }
}

left action {:layer 3} atomic_server2({:linear} i: One int)
modifies status;
{
    assert {:add_to_pool "A", i->val} status[i->val] == DEFAULT;
    status[i->val] := CREATED;
}
yield procedure {:layer 2} server2({:linear} i: One int);
refines atomic_server2;

yield procedure {:layer 3} client3({:linear} id: One int)
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

yield procedure {:layer 3} master3({:linear} id: One int)
refines atomic_master;
{
    call master2();
}

atomic action {:layer 3} atomic_master2()
modifies status;
{
    assert (forall {:pool "A"} i: int :: {:add_to_pool "A", i} 0 <= i && i < n ==> status[i] == PROCESSED);
    status := (lambda {:pool "A"} j: int :: if (0 <= j && j < n) then FINISHED else status[j]);
}
yield procedure {:layer 2} master2();
refines atomic_master2;
