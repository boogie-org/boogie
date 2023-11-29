// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} Tid = int;

const unique DEFAULT: int;
const unique CREATED: int;
const unique PROCESSED: int;
const unique FINISHED: int;

var status:[int]int;

const n: int;
axiom 0 <= n;

left action {:layer 1} AtomicCreateTask({:linear "tid"} tid: int)
modifies status;
{
    assert status[tid] == DEFAULT;
    status[tid] := CREATED;
}
yield procedure {:layer 0} CreateTask({:linear "tid"} tid: int);
refines AtomicCreateTask;

left action {:layer 1} AtomicProcessTask({:linear "tid"} tid: int)
modifies status;
{
    assert status[tid] == CREATED;
    status[tid] := PROCESSED;
}
yield procedure {:layer 0} ProcessTask({:linear "tid"} tid: int);
refines AtomicProcessTask;

left action {:layer 1} AtomicFinishTask({:linear "tid"} tid: int)
modifies status;
{
    assert status[tid] == PROCESSED;
    status[tid] := FINISHED;
}
yield procedure {:layer 0} FinishTask({:linear "tid"} tid: int);
refines AtomicFinishTask;

yield procedure {:layer 0} Alloc(i: int, {:linear_in "tid"} tidq: [int]bool) returns ({:linear "tid"} id: int, {:linear "tid"} tidq':[int]bool);
refines AtomicAlloc;
both action {:layer 1} AtomicAlloc(i: int, {:linear_in "tid"} tidq: [int]bool) returns ({:linear "tid"} id: int, {:linear "tid"} tidq':[int]bool)
{ assert tidq[i]; id := i; tidq' := tidq[i := false]; }

atomic action {:layer 2} AtomicMain({:linear_in "tid"} tids: [int]bool)
modifies status;
{
    assert (forall i: int :: 0 <= i && i < n <==> tids[i]);
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == DEFAULT);
    status := (lambda j: int :: if (0 <= j && j < n) then FINISHED else status[j]);
}

yield procedure {:layer 1} Main({:linear_in "tid"} tids: [int]bool)
refines AtomicMain;
{
    var i: int;
    var {:layer 1} snapshot: [int]int;
    var {:linear "tid"} tids': [int]bool;
    var {:linear "tid"} tid: int;

    i := 0;
    tids' := tids;
    call {:layer 1} snapshot := Copy(status);
    while (i < n)
    invariant {:layer 1} 0 <= i && i <= n;
    invariant {:layer 1} (forall j: int :: i <= j && j < n <==> tids'[j]);
    invariant {:layer 1} status == (lambda j: int :: if (0 <= j && j < i) then FINISHED else snapshot[j]);
    {
        call tid, tids' := Alloc(i, tids');
        async call {:sync} StartClient(tid);
        i := i + 1;
    }
}

yield left procedure {:layer 1} StartClient({:linear_in "tid"} tid: int)
modifies status;
requires {:layer 1} status[tid] == DEFAULT;
ensures {:layer 1} status == old(status)[tid := FINISHED];
{
    async call {:sync} GetTask(tid);
}

yield left procedure {:layer 1} GetTask({:linear_in "tid"} tid: int)
modifies status;
requires {:layer 1} status[tid] == DEFAULT;
ensures {:layer 1} status == old(status)[tid := FINISHED];
{
    call CreateTask(tid);
    async call {:sync} GetTaskCallback(tid);
}

yield left procedure {:layer 1} GetTaskCallback({:linear_in "tid"} tid: int)
modifies status;
requires {:layer 1} status[tid] == CREATED;
ensures {:layer 1} status == old(status)[tid := FINISHED];
{
    call ProcessTask(tid);
    async call {:sync} CollectTask(tid);
}

yield left procedure {:layer 1} CollectTask({:linear_in "tid"} tid: int)
modifies status;
requires {:layer 1} status[tid] == PROCESSED;
ensures {:layer 1} status == old(status)[tid := FINISHED];
{
    call FinishTask(tid);
}
