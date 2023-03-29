// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield invariant {:layer 100} Yield({:linear "tid"} tid:int);
invariant tid == GcTid;

const GcTid:int;

type {:linear "tid"} X = int;

procedure {:yields} {:layer 100} {:yield_requires "Yield", tid} Initialize({:linear "tid"} tid:int)
{
    call GarbageCollect(tid);

    call Yield(tid);

    async call GarbageCollect(tid);

    call Yield(tid);
}

procedure {:yields} {:layer 100} GarbageCollect({:linear "tid"} tid:int)
requires{:layer 100} tid == GcTid;
{
    call Yield(tid);
}
