// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"




const GcTid:int;

type {:linear "tid"} X = int;

procedure {:yields} {:layer 100} Initialize({:linear "tid"} tid:int)
requires{:layer 100} tid == GcTid;
{
    yield;
    assert{:layer 100} tid == GcTid;

    call GarbageCollect(tid);

    yield;
    assert{:layer 100} tid == GcTid;

    async call GarbageCollect(tid);

    yield;
    assert{:layer 100} tid == GcTid;

    async call GarbageCollect(tid);

    yield;
    assert{:layer 100} tid == GcTid;

    yield;
    assert{:layer 100} tid == GcTid;
}

procedure {:yields} {:layer 100} GarbageCollect({:linear "tid"} tid:int)
requires{:layer 100} tid == GcTid;
{
    yield;
    assert{:layer 100} tid == GcTid;
}
