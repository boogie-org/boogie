// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield invariant {:layer 100} Yield({:linear} tid: One int);
preserves tid->val == GcTid;

const GcTid:int;

yield procedure {:layer 100} Initialize({:linear} tid: One int)
requires call Yield(tid);
{
    call GarbageCollect(tid);

    call Yield(tid);

    async call GarbageCollect(tid);

    call Yield(tid);
}

yield procedure {:layer 100} GarbageCollect({:linear} tid: One int)
requires{:layer 100} tid->val == GcTid;
{
    call Yield(tid);
}
