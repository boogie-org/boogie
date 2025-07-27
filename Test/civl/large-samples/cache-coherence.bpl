// RUN: %parallel-boogie -vcsSplitOnEveryAssert "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
This example constructs a directory-based MESI cache coherence protocol.
Many important details of a realistic protocol are modeled.
- Individual steps taken by the cache and directory controllers are fine-grained.
- Operations on the cache controller are non-blocking.
- Multiple memory addresses may map to the same cache address.
- A cache line may be evicted nondeterministically.
*/

type MemAddr;
type CacheAddr;
function Hash(MemAddr): CacheAddr;
type Value;
type CacheId;
const i0: CacheId; // used for pool-based quantifier instantiation

datatype State {
  Modified(),
  Exclusive(),
  Shared(),
  Invalid()
}

function {:inline} Owned(state: State): bool {
  state == Exclusive() || state == Modified()
}

datatype Result {
  Ok(),
  Fail()
}

datatype CacheLine {
  CacheLine(ma: MemAddr, value: Value, state: State)
}

datatype DirState {
  Owner(i: CacheId),
  Sharers(iset: Set CacheId)
}

datatype CachePermission {
  CachePermission(i: CacheId, ca: CacheAddr)
}

datatype DirPermission {
  DirPermission(i: CacheId, ma: MemAddr)
}

function {:inline} WholeDirPermission(ma: MemAddr): Set DirPermission {
  Set((lambda {:pool "DirPermission"} x: DirPermission :: x->ma == ma))
}

// Implementation state
var {:layer 0,2} mem: [MemAddr]Value;
var {:layer 0,2} dir: [MemAddr]DirState;
var {:layer 0,1} dirBusy: [MemAddr]bool;
var {:layer 0,2} cache: [CacheId][CacheAddr]CacheLine;
var {:layer 0,1} cacheBusy: [CacheId][CacheAddr]bool;

// Auxiliary state to replace dirBusy and cacheBusy
var {:linear} {:layer 1,2} cachePermissions: Set CachePermission;
var {:linear} {:layer 1,2} dirPermissions: Set DirPermission;

// Specification state
var {:layer 1,3} absMem: [MemAddr]Value;

/// Proof intuition
/*
The proof is done in two layers.

Layer 1 to layer 2:
absMem is introduced to enable specification of the cache coherence property.
cachePermissions and dirPermissions are introduced allowing dirBusy and cacheBusy to be hidden.
The main purpose of this proof is to create atomic actions with suitable mover types.
Specifically, we want the following:
- Memory operations (read and write) to be both movers.
- Shared invalidate request at cache to be left mover.
- Response to read request at cache to be left mover.
- Initiation and conclusion of cache and directory operations to be right and left movers, respectively.

Layer 2 to layer 3:
We do an invariance proof to hide the directory and all the caches so that the read
and write operations at cache are described as atomic operations over absMem.
This specfication method naturally captures the cache coherence property.
To achieve this specfication, the variables mem, dir, cache, cachePermissions, and dirPermissions are hidden.
The yield invariant at this level is a global invariant connecting directory and cache states.
*/

/// Yield invariants
yield invariant {:layer 1} YieldInv#1();
invariant (forall i: CacheId, ca: CacheAddr:: Set_Contains(cachePermissions, CachePermission(i, ca)) || cacheBusy[i][ca]);
invariant (forall ma: MemAddr:: Set_IsSubset(WholeDirPermission(ma), dirPermissions) || dirBusy[ma]);

yield invariant {:layer 2} YieldInv#2();
invariant (forall i: CacheId, ca: CacheAddr:: Hash(cache[i][ca]->ma) == ca);
invariant (forall i: CacheId, ca: CacheAddr:: (var line := cache[i][ca];
              line->state == Invalid() ||
              (line->value == absMem[line->ma] && if line->state == Shared() then dir[line->ma] is Sharers else dir[line->ma] is Owner)));
invariant (forall ma: MemAddr:: {dir[ma]} dir[ma] is Owner ==> Owned(cache[dir[ma]->i][Hash(ma)]->state) && cache[dir[ma]->i][Hash(ma)]->ma == ma);
invariant (forall ma: MemAddr:: {dir[ma]} dir[ma] is Owner ==>
            (forall i: CacheId:: cache[i][Hash(ma)]->ma == ma ==> dir[ma]->i == i || cache[i][Hash(ma)]->state == Invalid()));
invariant (forall ma: MemAddr:: {dir[ma]} dir[ma] is Sharers ==>
            (forall i: CacheId:: Set_Contains(dir[ma]->iset, i) ==> cache[i][Hash(ma)]->state == Shared() && cache[i][Hash(ma)]->ma == ma));
invariant (forall ma: MemAddr:: {dir[ma]} dir[ma] is Sharers ==>
            (forall i: CacheId:: cache[i][Hash(ma)]->ma == ma ==> Set_Contains(dir[ma]->iset, i) || cache[i][Hash(ma)]->state == Invalid()));
invariant (forall ma: MemAddr:: {dir[ma]} dir[ma] is Sharers ==> mem[ma] == absMem[ma]);

yield invariant {:layer 2} YieldEvict(i: CacheId, ma: MemAddr, value: Value, {:linear} drp: Set CachePermission);
invariant Set_Contains(drp, CachePermission(i, Hash(ma)));
invariant value == cache[i][Hash(ma)]->value;

yield invariant {:layer 2} YieldRead(i: CacheId, ma: MemAddr, {:linear} drp: Set CachePermission);
invariant Set_Contains(drp, CachePermission(i, Hash(ma)));
invariant (var line := cache[i][Hash(ma)]; (line->state == Invalid() || line->state == Shared()) && line->ma == ma);

/// Cache
/*
There are 5 top-level operations on the cache:
- cache_read and cache_write read and write a cache entry, respectively.
- cache_evict_req initiates eviction of a cache line.
- cache_read_shd_req and cache_read_exc_req initiate bringing a memory address into the cache
  in Shared and Exclusive mode, respectively.
The last three operations make asynchronous calls to corresponding operations on the directory
to achieve their goals.

We introduce at layer 1 a global variable absMem to capture the logical view of memory.
The presence of absMem allows us to specify the cache coherence property in a natural way.
The verification demonstrates that at layer 3:
- cache_read is abstracted by an atomic action that reads from absMem.
- cache_write is abstracted by an atomic action that writes to absMem.
- all other operations are abstracted by "skip".
*/

yield procedure {:layer 2} cache_read(i: CacheId, ma: MemAddr) returns (result: Option Value)
preserves call YieldInv#2();
refines atomic action {:layer 3} _ {
  if (*) {
    result := None();
  } else {
    result := Some(absMem[ma]);
  }
}
{
  call result := cache_read#1(i, ma);
}

yield procedure {:layer 2} cache_write(i: CacheId, ma: MemAddr, v: Value) returns (result: Result)
preserves call YieldInv#1();
preserves call YieldInv#2();
refines atomic action {:layer 3} _ {
  if (*) {
    result := Fail();
  } else {
    result := Ok();
    absMem[ma] := v;
  }
}
{
  call result := cache_write#1(i, ma, v);
}

yield procedure {:layer 2} cache_evict_req(i: CacheId, ca: CacheAddr) returns (result: Result)
preserves call YieldInv#1();
preserves call YieldInv#2();
{
  var ma: MemAddr;
  var value: Value;
  var {:linear} {:layer 1,2} drp: Set CachePermission;
  
  call result, ma, value, drp := cache_evict_req#1(i, ca);
  if (result == Ok()) {
    async call dir_evict_req(i, ma, value, drp);
  }
}

yield procedure {:layer 2} cache_read_shd_req(i: CacheId, ma: MemAddr) returns (result: Result)
preserves call YieldInv#1();
preserves call YieldInv#2();
{
  var line: CacheLine;
  var {:linear} {:layer 1,2} drp: Set CachePermission;

  call result, drp := cache_read_shd_req#1(i, ma);
  if (result == Ok()) {
    async call dir_read_shd_req(i, ma, drp);
  }
}

yield procedure {:layer 2} cache_read_exc_req(i: CacheId, ma: MemAddr) returns (result: Result)
preserves call YieldInv#1();
preserves call YieldInv#2();
{
  var {:linear} {:layer 1,2} drp: Set CachePermission;

  call result, drp := cache_read_exc_req#1(i, ma);
  if (result == Ok()) {
    async call dir_read_exc_req(i, ma, drp);
  }
}

yield procedure {:layer 1} cache_read#1(i: CacheId, ma: MemAddr) returns (result: Option Value)
refines atomic action {:layer 2} _ {
  var ca: CacheAddr;
  var line: CacheLine;

  if (*) {
    // this relaxation allows cache_invalidate_shd#1 to commute to the left of cache_read#1
    result := Some(absMem[ma]);
  } else if (*) {
    result := None();
  } else {
    ca := Hash(ma);
    line := cache[i][ca];
    assume line->state != Invalid() && line->ma == ma;
    result := Some(line->value);
  }
}
{
  call result := cache_read#0(i, ma);
}

yield procedure {:layer 1} cache_write#1(i: CacheId, ma: MemAddr, v: Value) returns (result: Result)
preserves call YieldInv#1();
refines atomic action {:layer 2} _ {
  var ca: CacheAddr;
  var line: CacheLine;

  if (*) {
    result := Fail();
  } else {
    result := Ok();
    ca := Hash(ma);
    line := cache[i][ca];
    assume {:add_to_pool "X", i} line->state != Invalid() && line->state != Shared() && line->ma == ma && Set_Contains(cachePermissions, CachePermission(i, ca));
    cache[i][ca]->value := v;
    cache[i][ca]->state := Modified();
    absMem[ma] := v;
  }
}
{
  call result := cache_write#0(i, ma, v);
  if (result == Ok()) {
    call {:layer 1} absMem := Copy(absMem[ma := v]);
  }
}

yield procedure {:layer 1} cache_evict_req#1(i: CacheId, ca: CacheAddr) returns (result: Result, ma: MemAddr, value: Value, {:linear} {:layer 1} drp: Set CachePermission)
preserves call YieldInv#1();
refines atomic action {:layer 2} _ {
  var line: CacheLine;

  result := Fail();
  call drp := Set_MakeEmpty();
  if (*) {
    assume Set_Contains(cachePermissions, CachePermission(i, ca));
    call drp := Set_Get(cachePermissions, MapOne(CachePermission(i, ca)));
    line := cache[i][ca];
    ma := line->ma;
    value := line->value;
    result := Ok();
  }
}
{
  call result, ma, value := cache_evict_req#0(i, ca);
  call {:layer 1} drp := Set_MakeEmpty();
  if (result == Ok()) {
    call {:layer 1} drp := Set_Get(cachePermissions, MapOne(CachePermission(i, ca)));
  }
}

yield procedure {:layer 1} cache_read_shd_req#1(i: CacheId, ma: MemAddr) returns (result: Result, {:linear} {:layer 1} drp: Set CachePermission)
preserves call YieldInv#1();
refines atomic action {:layer 2} _ {
  var ca: CacheAddr;
  var line: CacheLine;

  result := Fail();
  ca := Hash(ma);
  line := cache[i][ca];
  call drp := Set_MakeEmpty();
  if (*) {
    assume line->state == Invalid();
    assume Set_Contains(cachePermissions, CachePermission(i, ca));
    call drp := Set_Get(cachePermissions, MapOne(CachePermission(i, ca)));
    cache[i][ca]->ma := ma;
    result := Ok();
  }
}
{
  call result := cache_read_shd_req#0(i, ma);
  call {:layer 1} drp := Set_MakeEmpty();
  if (result == Ok()) {
    call {:layer 1} drp := Set_Get(cachePermissions, MapOne(CachePermission(i, Hash(ma))));
  }
}

yield procedure {:layer 1} cache_read_exc_req#1(i: CacheId, ma: MemAddr) returns (result: Result, {:linear} {:layer 1} drp: Set CachePermission)
preserves call YieldInv#1();
refines atomic action {:layer 2} _ {
  var ca: CacheAddr;
  var line: CacheLine;

  result := Fail();
  ca := Hash(ma);
  line := cache[i][ca];
  call drp := Set_MakeEmpty();
  if (*) {
    assume line->state == Invalid() || (line->ma == ma && line->state == Shared());
    assume Set_Contains(cachePermissions, CachePermission(i, ca));
    call drp := Set_Get(cachePermissions, MapOne(CachePermission(i, ca)));
    cache[i][ca]->ma := ma;
    result := Ok();
  }
}
{
  call result := cache_read_exc_req#0(i, ma);
  call {:layer 1} drp := Set_MakeEmpty();
  if (result == Ok()) {
    call {:layer 1} drp := Set_Get(cachePermissions, MapOne(CachePermission(i, Hash(ma))));
  }
}

yield procedure {:layer 1} cache_nop_resp#1(i: CacheId, ma: MemAddr, {:linear_in} {:layer 1} drp: Set CachePermission, {:linear} {:layer 1} dp: Set DirPermission)
preserves call YieldInv#1();
refines atomic action {:layer 2} _ {
  assert Set_Contains(drp, CachePermission(i, Hash(ma)));
  assert dp == WholeDirPermission(ma);
  call Set_Put(cachePermissions, drp);
}
{
  call {:layer 1} Set_Put(cachePermissions, drp);
}

yield procedure {:layer 1} cache_evict_resp#1(i: CacheId, ma: MemAddr, {:linear_in} {:layer 1} drp: Set CachePermission, {:linear} {:layer 1} dp: Set DirPermission)
preserves call YieldInv#1();
refines atomic action {:layer 2} _ {
  var ca: CacheAddr;
  var line: CacheLine;

  ca := Hash(ma);
  line := cache[i][ca];
  assert Set_Contains(drp, CachePermission(i, ca));
  assert dp == WholeDirPermission(ma);
  assert line->ma == ma;
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  cache[i][ca]->state := Invalid();
  call Set_Put(cachePermissions, drp);
}
{
  call cache_evict_resp#0(i, ma);
  call {:layer 1} Set_Put(cachePermissions, drp);
}

/*
The left mover types of the actions cache_read_resp#1 and cache_invalidate_shd#1 are critical
to achieve the correct atomicity for the directory operations.
If the two invocations are hitting different caches, the argument is straightforward.
Otherwise, they are hitting the same cache and their i arguments are the same.
In this case, the conflict between their dp arguments implies that their ma arguments are different.
Call these arguments ma1 and ma2; let ca1 == Hash(ma1) and ca2 == Hash(ma2).
If ca1 and ca2 are different, there is no conflict.
Otherwise ca1 and ca2 are same.
We get a contradiction because both invocations are referring to the same cache line
but asserting that ma field of this cache line are equal to ma1 and ma2, respectively.
*/

yield procedure {:layer 1} cache_read_resp#1(i: CacheId, ma: MemAddr, v: Value, s: State, {:linear_in} {:layer 1} drp: Set CachePermission, {:linear} {:layer 1} dp: Set DirPermission)
preserves call YieldInv#1();
refines left action {:layer 2} _ {
  var ca: CacheAddr;
  var line: CacheLine;

  assert dp == WholeDirPermission(ma);  
  assert s == Shared() || s == Exclusive();
  ca := Hash(ma);
  assert Set_Contains(drp, CachePermission(i, ca));
  line := cache[i][ca];
  assert line->state == Invalid() || line->state == Shared();
  assert line->ma == ma;
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  if (line->state == Invalid()) {
    cache[i][ca] := CacheLine(ma, v, s);
  } else {
    cache[i][ca]->state := s;
  }
  call Set_Put(cachePermissions, drp);
}
{
  call cache_read_resp#0(i, ma, v, s);
  call {:layer 1} Set_Put(cachePermissions, drp);
}

yield procedure {:layer 1} cache_invalidate_shd#1(i: CacheId, ma: MemAddr, s: State, {:linear} {:layer 1} dp: Set DirPermission)
refines left action {:layer 2} _ {
  var ca: CacheAddr;

  assert Set_Contains(dp, DirPermission(i, ma));
  assume {:add_to_pool "DirPermission", DirPermission(i, ma)} true;
  ca := Hash(ma);
  assert (forall {:pool "X"} j: CacheId :: {:add_to_pool "X", j} (var line := cache[j][ca]; line->ma == ma ==> line->state == Invalid() || line->state == Shared()));
  // this assertion accompanies the relaxation in cache_read#1 to allow cache_invalidate_shd#1 to commute to the left of cache_read#1
  assert cache[i][ca]->value == absMem[ma];
  call primitive_cache_invalidate_shd(i, ma, s);
}
{
  call cache_invalidate_shd#0(i, ma, s);
}

yield procedure {:layer 1} cache_invalidate_exc#1(i: CacheId, ma: MemAddr, s: State, {:linear} {:layer 1} dp: Set DirPermission) returns (value: Value)
refines atomic action {:layer 2} _ {
  assert dp == WholeDirPermission(ma);
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  call value := primitive_cache_invalidate_exc(i, ma, s);
}
{
  call value := cache_invalidate_exc#0(i, ma, s);
}

// Cache primitives
yield procedure {:layer 0} cache_read#0(i: CacheId, ma: MemAddr) returns (result: Option Value);
refines atomic action {:layer 1} _ {
  var ca: CacheAddr;
  var line: CacheLine;

  ca := Hash(ma);
  line := cache[i][ca];
  result := None();
  if (line->state != Invalid() && line->ma == ma) {
    result := Some(line->value);
  }
}

yield procedure {:layer 0} cache_write#0(i: CacheId, ma: MemAddr, v: Value) returns (result: Result);
refines atomic action {:layer 1} _ {
  var ca: CacheAddr;
  var line: CacheLine;

  ca := Hash(ma);
  line := cache[i][ca];
  result := Fail();
  if (line->state != Invalid() && line->state != Shared() && line->ma == ma && !cacheBusy[i][ca]) {
    cache[i][ca]->value := v;
    cache[i][ca]->state := Modified();
    result := Ok();
  }
}

yield procedure {:layer 0} cache_evict_req#0(i: CacheId, ca: CacheAddr) returns (result: Result, ma: MemAddr, value: Value);
refines atomic action {:layer 1} _ {
  var line: CacheLine;

  line := cache[i][ca];
  ma := line->ma;
  value := line->value;
  if (line->state != Invalid()) {
    call result := acquire_cache_lock(i, ca);
  } else {
    result := Fail();
  }
}

yield procedure {:layer 0} cache_read_shd_req#0(i: CacheId, ma: MemAddr) returns (result: Result);
refines atomic action {:layer 1} _ {
  var ca: CacheAddr;
  var line: CacheLine;

  ca := Hash(ma);
  line := cache[i][ca];
  if (line->state == Invalid()) {
    call result := acquire_cache_lock(i, ca);
    if (result == Ok()) {
      cache[i][ca]->ma := ma;
    }
  } else {
    result := Fail();
  }
}

yield procedure {:layer 0} cache_read_exc_req#0(i: CacheId, ma: MemAddr) returns (result: Result);
refines atomic action {:layer 1} _ {
  var ca: CacheAddr;
  var line: CacheLine;

  ca := Hash(ma);
  line := cache[i][ca];
  if (line->state == Invalid() || (line->ma == ma && line->state == Shared())) {
    call result := acquire_cache_lock(i, ca);
    if (result == Ok()) {
      cache[i][ca]->ma := ma;
    }
  } else {
    result := Fail();
  }
}

action {:layer 1} acquire_cache_lock(i: CacheId, ca: CacheAddr) returns (result: Result)
modifies cache;
{
  if (!cacheBusy[i][ca]) {
    cacheBusy[i][ca] := true;
    result := Ok();
  } else {
    result := Fail();
  }
}

yield procedure {:layer 0} cache_evict_resp#0(i: CacheId, ma: MemAddr);
refines atomic action {:layer 1} _ {
  var ca: CacheAddr;
  var line: CacheLine;

  ca := Hash(ma);
  line := cache[i][ca];
  assert line->ma == ma;
  cache[i][ca]->state := Invalid();
  cacheBusy[i][ca] := false;
}

yield procedure {:layer 0} cache_read_resp#0(i: CacheId, ma: MemAddr, v: Value, s: State);
refines atomic action {:layer 1} _ {
  var ca: CacheAddr;
  var line: CacheLine;

  assert s == Shared() || s == Exclusive();
  ca := Hash(ma);
  line := cache[i][ca];
  assert line->state == Invalid() || line->state == Shared();
  assert line->ma == ma;
  cache[i][ca] := CacheLine(ma, if line->state == Invalid() then v else line->value, s);
  cacheBusy[i][ca] := false;
}

yield procedure {:layer 0} cache_invalidate_shd#0(i: CacheId, ma: MemAddr, s: State);
refines atomic action {:layer 1} _ {
  call primitive_cache_invalidate_shd(i, ma, s);
}

action {:layer 1,2} primitive_cache_invalidate_shd(i: CacheId, ma: MemAddr, s: State)
{
  var ca: CacheAddr;
  var line: CacheLine;

  assert s == Invalid();
  ca := Hash(ma);
  line := cache[i][ca];
  assert line->state == Shared();
  assert line->ma == ma;
  cache[i][ca]->state := s;
}

yield procedure {:layer 0} cache_invalidate_exc#0(i: CacheId, ma: MemAddr, s: State) returns (value: Value);
refines atomic action {:layer 1} _ {
  call value := primitive_cache_invalidate_exc(i, ma, s);
}

action {:layer 1,2} primitive_cache_invalidate_exc(i: CacheId, ma: MemAddr, s: State) returns (value: Value)
{
  var ca: CacheAddr;
  var line: CacheLine;

  assert s == Invalid() || s == Shared();
  ca := Hash(ma);
  line := cache[i][ca];
  assert line->state == Exclusive() || line->state == Modified();
  assert line->ma == ma;
  value := line->value;
  cache[i][ca]->state := s;
}

/// Directory
yield procedure {:layer 2} dir_evict_req(i: CacheId, ma: MemAddr, value: Value, {:layer 1,2} {:linear_in} drp: Set CachePermission)
preserves call YieldInv#1();
preserves call YieldInv#2();
requires call YieldEvict(i, ma, value, drp);
{
  var dirState: DirState;
  var {:linear} {:layer 1,2} dp: Set DirPermission;

  call dirState, dp := dir_req_begin(ma);
  // do not change dirState in case this is a stale evict request due to a race condition with an invalidate
  if (dirState == Owner(i)) {
    par write_mem(ma, value, dp) | YieldInv#1();
    dirState := Sharers(Set_Empty());
    call cache_evict_resp#1(i, ma, drp, dp);
  } else if (dirState is Sharers && Set_Contains(dirState->iset, i)) {
    dirState := Sharers(Set_Remove(dirState->iset, i));
    call cache_evict_resp#1(i, ma, drp, dp);
  } else {
    call cache_nop_resp#1(i, ma, drp, dp);
  }
  call dir_req_end(ma, dirState, dp);
}

yield procedure {:layer 2} dir_read_shd_req(i: CacheId, ma: MemAddr, {:layer 1,2} {:linear_in} drp: Set CachePermission)
preserves call YieldInv#1();
preserves call YieldInv#2();
requires call YieldRead(i, ma, drp);
{
  var dirState: DirState;
  var {:linear} {:layer 1,2} dp: Set DirPermission;
  var value: Value;

  call dirState, dp := dir_req_begin(ma);
  if (dirState is Owner) {
    par value := cache_invalidate_exc#1(dirState->i, ma, Shared(), dp) | YieldInv#1();
    par write_mem(ma, value, dp) | YieldInv#1();
    call cache_read_resp#1(i, ma, value, Shared(), drp, dp);
    call dir_req_end(ma, Sharers(Set_Add(Set_Add(Set_Empty(), dirState->i), i)), dp);
  } else {
    par value := read_mem(ma, dp) | YieldInv#1();
    call cache_read_resp#1(i, ma, value, if dirState->iset == Set_Empty() then Exclusive() else Shared(), drp, dp);
    call dir_req_end(ma, if dirState->iset == Set_Empty() then Owner(i) else Sharers(Set_Add(dirState->iset, i)), dp);
  }
}

yield procedure {:layer 2} dir_read_exc_req(i: CacheId, ma: MemAddr, {:layer 1,2} {:linear_in} drp: Set CachePermission)
preserves call YieldInv#1();
preserves call YieldInv#2();
requires call YieldRead(i, ma, drp);
{
  var dirState: DirState;
  var {:linear} {:layer 1,2} dp: Set DirPermission;
  var value: Value;

  call dirState, dp := dir_req_begin(ma);
  if (dirState is Owner) {
    par value := cache_invalidate_exc#1(dirState->i, ma, Invalid(), dp) | YieldInv#1();
    par write_mem(ma, value, dp) | YieldInv#1();
  } else {
    par dp := invalidate_sharers(ma, dirState->iset, dp) | YieldInv#1();
    par value := read_mem(ma, dp) | YieldInv#1();
  }
  call cache_read_resp#1(i, ma, value, Exclusive(), drp, dp);
  call dir_req_end(ma, Owner(i), dp);
}

yield left procedure {:layer 2} invalidate_sharers(ma: MemAddr, victims: Set CacheId, {:linear_in} {:layer 1,2} dp: Set DirPermission)
  returns ({:linear} {:layer 1,2} dp': Set DirPermission)
modifies cache;
requires {:layer 2} Set_IsSubset(Set((lambda x: DirPermission :: Set_Contains(victims, x->i) && x->ma == ma)), dp);
requires {:layer 2} (forall i: CacheId, ca: CacheAddr:: (var line := cache[i][ca];
                      line->state == Invalid() ||
                      (line->value == absMem[line->ma] && if line->state == Shared() then dir[line->ma] is Sharers else dir[line->ma] is Owner)));
requires {:layer 2} (forall i: CacheId:: Set_Contains(victims, i) ==> cache[i][Hash(ma)]->state == Shared() && cache[i][Hash(ma)]->ma == ma);
ensures {:layer 2} (forall i: CacheId:: Set_Contains(victims, i) ==> 
                        cache[i] == old(cache)[i][Hash(ma) := CacheLine(ma, old(cache)[i][Hash(ma)]->value, Invalid())]);
ensures {:layer 2} (forall i: CacheId:: Set_Contains(victims, i) || cache[i] == old(cache)[i]);
ensures {:layer 2} dp == dp';
{
  var victim: CacheId;
  var victims': Set CacheId;
  var {:linear} {:layer 1,2} dpOne: Set DirPermission;

  dp' := dp;
  if (victims == Set_Empty())
  {
    return;
  }
  victim := Choice(victims->val);
  victims' := Set_Remove(victims, victim);
  call dpOne, dp' := get_victim(victim, ma, dp');
  par cache_invalidate_shd#1(victim, ma, Invalid(), dpOne) | dp' := invalidate_sharers(ma, victims', dp');
  call dp' := put_victim(dpOne, dp');
}

yield procedure {:layer 1} get_victim(victim: CacheId, ma: MemAddr, {:layer 1} {:linear_in} dp: Set DirPermission)
returns ({:linear} {:layer 1} dpOne: Set DirPermission, {:linear} {:layer 1} dp': Set DirPermission)
refines both action {:layer 2} _ {
  dp' := dp;
  call dpOne := Set_Get(dp', MapOne(DirPermission(victim, ma)));
}
{
  dp' := dp;
  call {:layer 1} dpOne := Set_Get(dp', MapOne(DirPermission(victim, ma)));
}

yield procedure {:layer 1} put_victim({:linear_in} {:layer 1} dpOne: Set DirPermission, {:layer 1} {:linear_in} dp: Set DirPermission)
returns ({:linear} {:layer 1} dp': Set DirPermission)
refines both action {:layer 2} _ {
  dp' := dp;
  call Set_Put(dp', dpOne);
}
{
  dp' := dp;
  call {:layer 1} Set_Put(dp', dpOne);
}

yield procedure {:layer 1} dir_req_begin(ma: MemAddr) returns (dirState: DirState, {:linear} {:layer 1} dp: Set DirPermission)
preserves call YieldInv#1();
refines right action {:layer 2} _ {
  assume Set_IsSubset(WholeDirPermission(ma), dirPermissions);
  dirState := dir[ma];
  call dp := Set_Get(dirPermissions, WholeDirPermission(ma)->val);
}
{
  call dirState := dir_req_begin#0(ma);
  call {:layer 1} dp := Set_Get(dirPermissions, WholeDirPermission(ma)->val);
}

yield procedure {:layer 1} dir_req_end(ma: MemAddr, dirState: DirState, {:layer 1} {:linear_in} dp: Set DirPermission)
preserves call YieldInv#1();
refines left action {:layer 2} _ {
  assert dp == WholeDirPermission(ma);
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  dir[ma] := dirState;
  call Set_Put(dirPermissions, dp);
}
{
  call dir_req_end#0(ma, dirState);
  call {:layer 1} Set_Put(dirPermissions, dp);
}

// Directory primitives
yield procedure {:layer 0} dir_req_begin#0(ma: MemAddr) returns (dirState: DirState);
refines atomic action {:layer 1} _ {
  assume !dirBusy[ma];
  dirBusy[ma] := true;
  dirState := dir[ma];
}

yield procedure {:layer 0} dir_req_end#0(ma: MemAddr, dirState: DirState);
refines atomic action {:layer 1} _ {
  dir[ma] := dirState;
  dirBusy[ma] := false;
}

/// Memory
yield procedure {:layer 1} read_mem(ma: MemAddr, {:linear} {:layer 1} dp: Set DirPermission) returns (value: Value)
refines both action {:layer 2} _ {
  assert dp == WholeDirPermission(ma);
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  value := mem[ma];
}
{
  call value := read_mem#0(ma);
}

yield procedure {:layer 1} write_mem(ma: MemAddr, value: Value, {:linear} {:layer 1} dp: Set DirPermission)
refines both action {:layer 2} _ {
  assert dp == WholeDirPermission(ma);
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  mem[ma] := value;
}
{
  call write_mem#0(ma, value);
}

// Memory primitives
yield procedure {:layer 0} read_mem#0(ma: MemAddr) returns (value: Value);
refines atomic action {:layer 1} _ {
  value := mem[ma];
}

yield procedure {:layer 0} write_mem#0(ma: MemAddr, value: Value);
refines atomic action {:layer 1} _ {
  mem[ma] := value;
}

