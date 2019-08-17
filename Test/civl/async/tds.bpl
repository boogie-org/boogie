// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "MapConst"} MapConstBool(bool): [int]bool;
function {:inline} {:linear "tid"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [int]bool) : [int]bool
{
  x
}

const unique DEFAULT: int;
const unique CREATED: int;
const unique PROCESSED: int;
const unique FINISHED: int;

var status:[int]int;

procedure {:atomic} {:layer 5} atomic_main({:linear "tid"} id: int, {:linear_in "tid"} tids: [int]bool)
modifies status;
{
    assert id == c;
    assert (forall i: int :: (0 <= i && i < n) <==> tids[i]);    
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == DEFAULT);
    status := (lambda j: int :: if (0 <= j && j < n) then FINISHED else status[j]);
}

procedure {:left} {:layer 4} atomic_server({:linear "tid"} id: int, {:linear_in "tid"} tids: [int]bool)
modifies status;
{
    assert id == c;
    assert (forall i: int :: (0 <= i && i < n) <==> tids[i]);
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == DEFAULT);
    status := (lambda j: int :: if (0 <= j && j < n) then CREATED else status[j]);
}

procedure {:left} {:layer 4} atomic_client({:linear "tid"} id: int)
modifies status;
{
    assert id == c;
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == CREATED);
    status := (lambda j: int :: if (0 <= j && j < n) then PROCESSED else status[j]);
}

procedure {:left} {:layer 4} atomic_master({:linear "tid"} id: int)
modifies status;
{
    assert id == c;
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == PROCESSED);
    status := (lambda j: int :: if (0 <= j && j < n) then FINISHED else status[j]);
}

const c: int;
const n: int;
axiom 0 <= n;

procedure {:yields} {:layer 4} {:refines "atomic_main"} main({:linear "tid"} id: int, {:linear_in "tid"} tids: [int]bool)
{
    var i: int;
    var sid: int;
    var mid: int;
    var cid: int;

    yield;
    call server3(id, tids);
    call client3(id);
    call master3(id);
    yield;
}

procedure {:layer 3} StatusSnapshot() returns (snapshot: [int]int);
ensures snapshot == status;

procedure {:yields} {:layer 2} {:refines "AtomicAlloc"} Alloc(i: int, {:linear_in "tid"} tidq: [int]bool) returns ({:linear "tid"} id: int, {:linear "tid"} tidq':[int]bool);
procedure {:both} {:layer 3} AtomicAlloc(i: int, {:linear_in "tid"} tidq: [int]bool) returns ({:linear "tid"} id: int, {:linear "tid"} tidq':[int]bool)
{ assert tidq[i]; id := i; tidq' := tidq[i := false]; }

procedure {:yields} {:layer 3} {:refines "atomic_server"} server3({:linear "tid"} id: int, {:linear_in "tid"} tids: [int]bool)
{
    var i: int;
    var {:layer 3} snapshot: [int]int;
    var {:linear "tid"} tids': [int]bool;
    var {:linear "tid"} tid: int;
    yield;
    i := 0;
    call snapshot := StatusSnapshot();
    tids' := tids;
    while (i < n)
    invariant {:terminates} {:layer 2,3} true;
    invariant {:layer 3} 0 <= i && i <= n;
    invariant {:layer 3} (forall j: int :: i <= j && j < n <==> tids'[j]);
    invariant {:layer 3} status == (lambda j: int :: if (0 <= j && j < i) then CREATED else snapshot[j]);
    {
        call tid, tids' := Alloc(i, tids');
        async call server2(tid);
        i := i + 1;
    }
    yield;
}

procedure {:left} {:layer 3} atomic_server2({:linear "tid"} i: int)
modifies status;
{
    assert status[i] == DEFAULT;
    status[i] := CREATED;
}
procedure {:yields} {:layer 2} {:refines "atomic_server2"} server2({:linear "tid"} i: int);

procedure {:yields} {:layer 3} {:refines "atomic_client"} client3({:linear "tid"} id: int)
{
    yield;
    call client2();
    yield;
}

procedure {:atomic} {:layer 3} atomic_client2()
modifies status;
{
    assume (forall i: int :: 0 <= i && i < n ==> status[i] == CREATED);
    status := (lambda j: int :: if (0 <= j && j < n) then PROCESSED else status[j]);
}
procedure {:yields} {:layer 2} {:refines "atomic_client2"} client2();

procedure {:yields} {:layer 3} {:refines "atomic_master"} master3({:linear "tid"} id: int)
{
    yield;
    call master2();
    yield;
}

procedure {:atomic} {:layer 3} atomic_master2()
modifies status;
{
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == PROCESSED);
    status := (lambda j: int :: if (0 <= j && j < n) then FINISHED else status[j]);    
}
procedure {:yields} {:layer 2} {:refines "atomic_master2"} master2();

