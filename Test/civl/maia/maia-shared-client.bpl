const unique tid: Tid;
const unique tid_0: Tid;
const unique tid_1: Tid;

yield invariant {:layer 1} ChildSharesInv(
    {:linear} signal: One SemSignal, {:linear} share: One MemShare);
preserves Map_Contains(semaphores, One(signal->val->sem_id));
preserves Map_Contains(Map_At(semaphores, One(signal->val->sem_id))->expected_mem_ids, signal->val);
preserves Map_At(Map_At(semaphores, One(signal->val->sem_id))->expected_mem_ids, signal->val) == Set_Empty();
preserves Map_Contains(Map_At(semaphores, One(signal->val->sem_id))->expected_mem_shares, signal->val);
preserves Map_At(Map_At(semaphores, One(signal->val->sem_id))->expected_mem_shares, signal->val) ==
    Set_Singleton(share);
free preserves !Map_Contains(Map_At(semaphores, One(signal->val->sem_id))->done, signal);

yield procedure {:layer 1} Main(
    {:linear_in} init_sem_id: One SemId, {:linear_in} init_signals: UnitMap (One SemSignal),
    {:linear} wait: One SemWait,
    {:linear_in} init_mem_id: One MemId, {:linear_in} init_shares: UnitMap (One MemShare))
    returns ({:linear} sem_id: One SemId, {:linear} signals: UnitMap (One SemSignal),
    {:linear} mem_id: One MemId, {:linear} shares: UnitMap (One MemShare))
requires {:layer 1} wait->val->sem_id == init_sem_id->val;
requires {:layer 1} AllSemaphoreSignals(init_sem_id, init_signals);
requires {:layer 1} AllMemShares(init_mem_id, init_shares);
preserves call SemaphoreInv();
ensures {:layer 1} sem_id == init_sem_id;
ensures {:layer 1} AllSemaphoreSignals(sem_id, signals);
ensures {:layer 1} AllMemShares(mem_id, shares);
ensures {:layer 1} mem_id == init_mem_id;
{
    var value: Value;
    var returned_shares: UnitMap (One MemShare);
    var share, share_0, share_1: One MemShare;
    var ord_shares: [One MemShare]bool;
    var done: UnitMap (One SemSignal);
    var signal_0, signal_1: One SemSignal;
    var awaited: [One SemSignal]bool;
    var expected_mem_ids: Map SemSignal ([One MemId]bool);
    var expected_mem_shares: Map SemSignal ([One MemShare]bool);
    var returned_mem: Map (One MemId) Value;

    mem_id := init_mem_id;
    share := One(MemShare(init_mem_id->val, tid));
    share_0 := One(MemShare(init_mem_id->val, tid_0));
    share_1 := One(MemShare(init_mem_id->val, tid_1));
    ord_shares := Set_Add(Set_Singleton(share_0), share_1);
    ord_shares := Set_Add(ord_shares, share);
    call MoveToShared(mem_id, 0 /* arbitrary value */, ord_shares);
    shares := init_shares;
    call One_Get(shares, share);
    call One_Get(shares, share_0);
    call One_Get(shares, share_1);

    signal_0 := One(SemSignal(init_sem_id->val, tid_0));
    signal_1 := One(SemSignal(init_sem_id->val, tid_1));
    awaited := Set_Add(Set_Singleton(signal_0), signal_1);
    expected_mem_ids := Map_Singleton(signal_0->val, Set_Empty());
    expected_mem_ids := Map_Update(expected_mem_ids, signal_1->val, Set_Empty());
    expected_mem_shares := Map_Singleton(signal_0->val, Set_Singleton(share_0));
    expected_mem_shares := Map_Update(expected_mem_shares, signal_1->val, Set_Singleton(share_1));
    call SemaphoreInv() |
         SharedReadInv(share_0) | SharedReadInv(share_1) |
         ExpectedImmMemContentsInv(share, ord_shares);
    call Publish(init_sem_id, awaited, expected_mem_ids, expected_mem_shares);
    signals := init_signals;
    call One_Get(signals, signal_0);
    call One_Get(signals, signal_1);
    async call Child(signal_0, share_0);
    async call Child(signal_1, share_1);
    call SemaphoreInv() | SemaphoreWaitInv(wait) |
         ExpectedSemaphoreContentsInv(wait, awaited, expected_mem_ids, expected_mem_shares) |
         ExpectedImmMemContentsInv(share, ord_shares);
    call sem_id, done, returned_mem, returned_shares := Wait(wait);
    call Map_Join(signals, done);
    call Map_Join(shares, returned_shares);
    call One_Put(shares, share);
    call SemaphoreInv() | ReclaimMemIdInv(init_mem_id->val, shares);
    call mem_id, value := MoveFromShared(init_mem_id->val, shares);
}

yield procedure {:layer 1} Child(
    {:linear_in} signal: One SemSignal, {:linear_in} share: One MemShare)
requires call SemaphoreSignalInv(signal);
requires call SharedReadInv(share);
requires call ChildSharesInv(signal, share);
preserves call SemaphoreInv();
{
    var value: Value;
    var mem: Map (One MemId) Value;
    var shares: UnitMap (One MemShare);

    call value := ReadFromShared(share);
    call SemaphoreInv() | SemaphoreSignalInv(signal) |
         SharedReadInv(share) | ChildSharesInv(signal, share);
    call mem := Map_MakeEmpty();
    call shares := Map_MakeEmpty();
    call One_Put(shares, share);
    call Signal(signal, mem, shares);
}
