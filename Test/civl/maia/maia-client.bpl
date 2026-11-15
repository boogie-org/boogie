// RUN: %parallel-boogie "%s" "%S/maia.bpl" > "%t"
// RUN: %diff "%s.expect" "%t"

const unique mem_id_0: MemId;
const unique mem_id_1: MemId;

yield invariant {:layer 1} Yield();

yield invariant {:layer 1} MainExpectedMemInv(
    {:linear} wait: One SemWait, expected_mem_ids: Map SemSignal ([One MemId]bool),
    awaited: [One SemSignal]bool);
preserves Map_Contains(semaphores, One(wait->val->sem_id));
preserves Map_At(semaphores, One(wait->val->sem_id))->expected_mem_ids == expected_mem_ids;
preserves Map_At(semaphores, One(wait->val->sem_id))->awaited == awaited;

yield procedure {:layer 1} Main(
    {:linear_in} initial_sem_id: One SemId, {:linear} wait: One SemWait,
    {:linear_in} initial_mem: Map (One MemId) Value)
    returns ({:linear} sem_id: One SemId, {:linear} mem: Map (One MemId) Value)
requires {:layer 1} wait->val->sem_id == initial_sem_id->val;
requires {:layer 1} Map_Contains(initial_mem, One(mem_id_0));
requires {:layer 1} Map_Contains(initial_mem, One(mem_id_1));
requires call SemaphorePublishInv(initial_sem_id);
preserves call SemaphoreInv();
ensures call SemaphorePublishInv(sem_id);
{
    var signals: UnitMap (One SemSignal);
    var awaited: [One SemSignal]bool;
    var first_signal, second_signal: One SemSignal;
    var first_mem, second_mem: Map (One MemId) Value;
    var mem_shares: UnitMap (One MemShare);
    var expected_mem_ids: Map SemSignal ([One MemId]bool);
    var expected_mem_shares: Map SemSignal ([One MemShare]bool);
    var observed: Value;

    mem := initial_mem;
    call mem, observed := AccessMemory(mem, mem_id_0);
    call mem, observed := AccessMemory(mem, mem_id_1);
    first_signal := One(SemSignal(initial_sem_id->val, 0));
    second_signal := One(SemSignal(initial_sem_id->val, 1));
    expected_mem_ids := Map_Singleton(first_signal->val, Set_Singleton(One(mem_id_0)));
    expected_mem_ids := Map_Update(expected_mem_ids, second_signal->val, Set_Singleton(One(mem_id_1)));
    expected_mem_shares := Map_Singleton(first_signal->val, Set_Empty());
    expected_mem_shares := Map_Update(expected_mem_shares, second_signal->val, Set_Empty());
    awaited := Set_Add(Set_Singleton(first_signal), second_signal);
    call signals := Publish(initial_sem_id, awaited,
                            expected_mem_ids, expected_mem_shares);
    call One_Get(signals, first_signal);
    call One_Get(signals, second_signal);
    call first_mem := Map_Split(mem, Set_Singleton(One(mem_id_0)));
    call second_mem := Map_Split(mem, Set_Singleton(One(mem_id_1)));
    async call Child(first_signal, first_mem, mem_id_0);
    async call Child(second_signal, second_mem, mem_id_1);
    call SemaphoreInv() | SemaphoreWaitInv(wait) | MainExpectedMemInv(wait, expected_mem_ids, awaited);
    call sem_id, mem, mem_shares := Wait(wait);
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

yield procedure {:layer 1} Child(
    {:linear_in} signal: One SemSignal, {:linear_in} initial_mem: Map (One MemId) Value,
    location: MemId)
requires {:layer 1} Map_Contains(initial_mem, One(location));
requires call SemaphoreSignalInv(signal);
requires call ChildExpectedMemInv(signal, initial_mem);
{
    var mem: Map (One MemId) Value;
    var shares: UnitMap (One MemShare);
    var observed: Value;

    call mem, observed := AccessMemory(initial_mem, location);
    call shares := Map_MakeEmpty();
    call Signal(signal, mem, shares);
}

pure action AccessMemory({:linear_in} initial_mem: Map (One MemId) Value,
                         location: MemId)
    returns ({:linear} mem: Map (One MemId) Value, observed: Value)
{
    mem := initial_mem;
    assert Map_Contains(mem, One(location));
    call observed := Path_Load(mem->val[One(location)]);
    call Path_Store(mem->val[One(location)], 0);
}

