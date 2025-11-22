// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Tid = int;

const unique DEFAULT: int;
const unique CREATED: int;
const unique PROCESSED: int;
const unique FINISHED: int;

var status:[int]int;

const n: int;
axiom 0 <= n;

left action {:layer 1} AtomicCreateTask({:linear} tid: One int)
modifies status;
{
    assert status[tid->val] == DEFAULT;
    status[tid->val] := CREATED;
}
yield procedure {:layer 0} CreateTask({:linear} tid: One int);
refines AtomicCreateTask;

left action {:layer 1} AtomicProcessTask({:linear} tid: One int)
modifies status;
{
    assert status[tid->val] == CREATED;
    status[tid->val] := PROCESSED;
}
yield procedure {:layer 0} ProcessTask({:linear} tid: One int);
refines AtomicProcessTask;

left action {:layer 1} AtomicFinishTask({:linear} tid: One int)
modifies status;
{
    assert status[tid->val] == PROCESSED;
    status[tid->val] := FINISHED;
}
yield procedure {:layer 0} FinishTask({:linear} tid: One int);
refines AtomicFinishTask;

yield procedure {:layer 0} Alloc(i: int, {:linear_in} tidq: Set (One int)) returns ({:linear} id: One int, {:linear} tidq': Set (One int));
refines AtomicAlloc;
both action {:layer 1} AtomicAlloc(i: int, {:linear_in} tidq: Set (One int)) returns ({:linear} id: One int, {:linear} tidq': Set (One int))
{ tidq' := tidq; id := One(i); call One_Split(tidq', id); }

atomic action {:layer 2} AtomicMain({:linear_in} tids: Set (One int))
modifies status;
{
    assert (forall i: int :: 0 <= i && i < n <==> Set_Contains(tids, One(i)));
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == DEFAULT);
    status := (lambda j: int :: if (0 <= j && j < n) then FINISHED else status[j]);
}

yield procedure {:layer 1} Main({:linear_in} tids: Set (One int))
refines AtomicMain;
{
    var i: int;
    var {:layer 1} snapshot: [int]int;
    var {:linear} tids': Set (One int);
    var {:linear} tid: One int;

    i := 0;
    tids' := tids;
    call {:layer 1} snapshot := Copy(status);
    while (i < n)
    invariant {:layer 1} 0 <= i && i <= n;
    invariant {:layer 1} (forall j: int :: i <= j && j < n <==> Set_Contains(tids', One(j)));
    invariant {:layer 1} status == (lambda j: int :: if (0 <= j && j < i) then FINISHED else snapshot[j]);
    {
        call tid, tids' := Alloc(i, tids');
        async call {:sync} StartClient(tid);
        i := i + 1;
    }
}

yield left procedure {:layer 1} StartClient({:linear_in} tid: One int)
modifies status;
requires {:layer 1} status[tid->val] == DEFAULT;
ensures {:layer 1} status == old(status)[tid->val := FINISHED];
{
    async call {:sync} GetTask(tid);
}

yield left procedure {:layer 1} GetTask({:linear_in} tid: One int)
modifies status;
requires {:layer 1} status[tid->val] == DEFAULT;
ensures {:layer 1} status == old(status)[tid->val := FINISHED];
{
    call CreateTask(tid);
    async call {:sync} GetTaskCallback(tid);
}

yield left procedure {:layer 1} GetTaskCallback({:linear_in} tid: One int)
modifies status;
requires {:layer 1} status[tid->val] == CREATED;
ensures {:layer 1} status == old(status)[tid->val := FINISHED];
{
    call ProcessTask(tid);
    async call {:sync} CollectTask(tid);
}

yield left procedure {:layer 1} CollectTask({:linear_in} tid: One int)
modifies status;
requires {:layer 1} status[tid->val] == PROCESSED;
ensures {:layer 1} status == old(status)[tid->val := FINISHED];
{
    call FinishTask(tid);
}
