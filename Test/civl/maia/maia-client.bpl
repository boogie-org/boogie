// RUN: %parallel-boogie "%s" "%S/maia.bpl" > "%t"
// RUN: %diff "%s.expect" "%t"

const unique mem_id_0: MemId;
const unique mem_id_1: MemId;

const unique tid_0: Tid;
const unique tid_1: Tid;

yield procedure {:layer 1} Main(
    {:linear_in} init_sem_id: One SemId, {:linear_in} init_signals: UnitMap (One SemSignal),
    {:linear} wait: One SemWait,
    {:linear_in} init_mem: Map (One MemId) Value)
    returns ({:linear} sem_id: One SemId, {:linear} signals: UnitMap (One SemSignal), {:linear} mem: Map (One MemId) Value)
requires {:layer 1} wait->val->sem_id == init_sem_id->val;
requires {:layer 1} Map_Contains(init_mem, One(mem_id_0));
requires {:layer 1} Map_Contains(init_mem, One(mem_id_1));
requires {:layer 1} AllSemaphoreSignals(init_sem_id, init_signals);
preserves call SemaphoreInv();
ensures {:layer 1} sem_id == init_sem_id;
ensures {:layer 1} AllSemaphoreSignals(sem_id, signals);
{
    var done: UnitMap (One SemSignal);
    var awaited: [One SemSignal]bool;
    var signal_0, signal_1: One SemSignal;
    var mem_0, mem_1: Map (One MemId) Value;
    var mem_shares: UnitMap (One MemShare);
    var expected_mem_ids: Map SemSignal ([One MemId]bool);
    var expected_mem_shares: Map SemSignal ([One MemShare]bool);
    var observed: Value;

    mem := init_mem;
    call mem, observed := AccessMemory(mem, mem_id_0);
    call mem, observed := AccessMemory(mem, mem_id_1);
    signal_0 := One(SemSignal(init_sem_id->val, tid_0));
    signal_1 := One(SemSignal(init_sem_id->val, tid_1));
    expected_mem_ids := Map_Singleton(signal_0->val, Set_Singleton(One(mem_id_0)));
    expected_mem_ids := Map_Update(expected_mem_ids, signal_1->val, Set_Singleton(One(mem_id_1)));
    expected_mem_shares := Map_Singleton(signal_0->val, Set_Empty());
    expected_mem_shares := Map_Update(expected_mem_shares, signal_1->val, Set_Empty());
    awaited := Set_Add(Set_Singleton(signal_0), signal_1);
    call Publish(init_sem_id, awaited, expected_mem_ids, expected_mem_shares);
    signals := init_signals;
    call One_Get(signals, signal_0);
    call One_Get(signals, signal_1);
    call mem_0 := Map_Split(mem, Set_Singleton(One(mem_id_0)));
    call mem_1 := Map_Split(mem, Set_Singleton(One(mem_id_1)));
    async call Child(signal_0, mem_0, mem_id_0);
    async call Child(signal_1, mem_1, mem_id_1);
    call SemaphoreInv() | SemaphoreWaitInv(wait) |
         ExpectedSemaphoreContentsInv(wait, awaited, expected_mem_ids, expected_mem_shares);
    call sem_id, done, mem, mem_shares := Wait(wait);
    call Map_Join(signals, done);
    call mem, observed := AccessMemory(mem, mem_id_0);
    call mem, observed := AccessMemory(mem, mem_id_1);
}

yield invariant {:layer 1} ChildExpectedMemInv(
    {:linear} signal: One SemSignal, {:linear} mem: Map (One MemId) Value);
preserves Map_Contains(semaphores, One(signal->val->sem_id));
preserves Map_Contains(Map_At(semaphores, One(signal->val->sem_id))->expected_mem_ids, signal->val);
preserves Map_At(Map_At(semaphores, One(signal->val->sem_id))->expected_mem_ids, signal->val) == mem->dom;
preserves Map_Contains(Map_At(semaphores, One(signal->val->sem_id))->expected_mem_shares, signal->val);
preserves Map_At(Map_At(semaphores, One(signal->val->sem_id))->expected_mem_shares, signal->val) == Set_Empty();
free preserves !Map_Contains(Map_At(semaphores, One(signal->val->sem_id))->done, signal);

yield procedure {:layer 1} Child(
    {:linear_in} signal: One SemSignal, {:linear_in} init_mem: Map (One MemId) Value,
    location: MemId)
requires {:layer 1} Map_Contains(init_mem, One(location));
requires call SemaphoreSignalInv(signal);
requires call ChildExpectedMemInv(signal, init_mem);
{
    var mem: Map (One MemId) Value;
    var shares: UnitMap (One MemShare);
    var observed: Value;

    call mem, observed := AccessMemory(init_mem, location);
    call shares := Map_MakeEmpty();
    call Signal(signal, mem, shares);
}

pure action AccessMemory({:linear_in} init_mem: Map (One MemId) Value,
                         location: MemId)
    returns ({:linear} mem: Map (One MemId) Value, observed: Value)
{
    mem := init_mem;
    assert Map_Contains(mem, One(location));
    call observed := Path_Load(mem->val[One(location)]);
    call Path_Store(mem->val[One(location)], 0);
}

