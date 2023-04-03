// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield invariant {:layer 100} Yield({:linear "tid"} tid:int);
invariant tid == GcTid;

const GcTid:int;

type {:linear "tid"} X = int;

yield procedure {:layer 100} Initialize({:linear "tid"} tid:int)
requires call Yield(tid);
{
    call GarbageCollect(tid);

    call Yield(tid);

    async call GarbageCollect(tid);

    call Yield(tid);
}

yield procedure {:layer 100} GarbageCollect({:linear "tid"} tid:int)
requires{:layer 100} tid == GcTid;
{
    call Yield(tid);
}
