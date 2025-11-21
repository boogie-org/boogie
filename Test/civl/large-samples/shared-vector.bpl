// RUN: %parallel-boogie -timeLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

////////////////////////////////////////////////////////////////////////////////
// Shared integer array implementation

var {:layer 2, 3} IntArrayPool: Map (One (Loc IntArray)) (Vec int);

datatype IntArray {
  IntArray(
    {:linear "no_collect_keys"} mutexes: Map int (One (Loc int)),
    {:linear "no_collect_keys"} values: Map int (Cell (Loc int) int)
  )
}

var {:layer 0, 2} {:linear} IntArrayPoolLow: Map (One (Loc IntArray)) IntArray;

yield invariant {:layer 2} IntArrayDom();
preserves IntArrayPool->dom == IntArrayPoolLow->dom;

yield invariant {:layer 2} Yield(loc_iv: Loc IntArray);
preserves Map_Contains(IntArrayPoolLow, One(loc_iv));
preserves
  (var intvec_low, intvec_high := Map_At(IntArrayPoolLow, One(loc_iv)), Map_At(IntArrayPool, One(loc_iv));
    intvec_low->mutexes->dom == intvec_low->values->dom &&
    intvec_low->mutexes->dom->val == (lambda i: int :: 0 <= i && i < Vec_Len(intvec_high)) &&
    (forall j: int:: 0 <= j && j < Vec_Len(intvec_high) ==> Map_Contains(MutexPool, Map_At(intvec_low->mutexes, j)->val)) &&
    (forall j: int:: 0 <= j && j < Vec_Len(intvec_high) ==> Map_At(intvec_low->values, j)->val == Vec_Nth(intvec_high, j)));

atomic action {:layer 3} Atomic_IntArray_Alloc(v: Vec int) returns (loc_iv: Loc IntArray)
modifies IntArrayPool;
{
  var {:linear} one_loc_iv: One (Loc IntArray);
  call one_loc_iv := Loc_New();
  loc_iv := one_loc_iv->val;
  assume !Map_Contains(IntArrayPool, One(loc_iv));
  IntArrayPool := Map_Update(IntArrayPool, One(loc_iv), v);
}
yield procedure {:layer 2} IntArray_Alloc(v: Vec int) returns (loc_iv: Loc IntArray)
refines Atomic_IntArray_Alloc;
ensures call Yield(loc_iv);
preserves call IntArrayDom();
{
  var {:linear} one_loc_mutex: One (Loc int);
  var {:linear} cell_int: Cell (Loc int) int;
  var {:linear "no_collect_keys"} mutexes: Map int (One (Loc int));
  var {:linear "no_collect_keys"} values: Map int (Cell (Loc int) int);
  var {:linear} intvec: IntArray;
  var i: int;
  var {:linear} one_loc_i: One (Loc int);
  var {:linear} one_loc_iv: One (Loc IntArray);
  var {:layer 2} OldMutexPool: Map (Loc int) Mutex;

  call mutexes := Map_MakeEmpty();
  call values := Map_MakeEmpty();

  call {:layer 2} OldMutexPool := Copy(MutexPool);
  i := 0;
  while (i < Vec_Len(v))
  invariant {:layer 2} 0 <= i && i <= Vec_Len(v);
  invariant {:layer 2} mutexes->dom == values->dom;
  invariant {:layer 2} mutexes->dom->val == (lambda j: int :: 0 <= j && j < i);
  invariant {:layer 2} (forall j: int:: 0 <= j && j < i ==> Map_Contains(MutexPool, Map_At(mutexes, j)->val));
  invariant {:layer 2} (forall j: int:: 0 <= j && j < i ==> Map_At(values, j)->val == Vec_Nth(v, j));
  invariant {:layer 2} Set_IsSubset(OldMutexPool->dom, MutexPool->dom);
  {
    call one_loc_mutex := Mutex_Alloc();
    call Map_PutValue(mutexes, i, one_loc_mutex);
    call one_loc_i := Loc_New();
    cell_int := Cell(one_loc_i, Vec_Nth(v, i));
    call Map_PutValue(values, i, cell_int);
    i := i + 1;
  }

  intvec := IntArray(mutexes, values);
  call one_loc_iv := Loc_New();
  loc_iv := one_loc_iv->val;
  call AddIntArrayToPool(one_loc_iv, intvec);
  call {:layer 2} IntArrayPool := Copy(Map_Update(IntArrayPool, one_loc_iv, v));
}

atomic action {:layer 3} Atomic_IntArray_Read({:linear} tid: One Tid, loc_iv: Loc IntArray, i: int) returns (v: int)
{
  var vec: Vec int;
  assert Map_Contains(IntArrayPool, One(loc_iv));
  vec := Map_At(IntArrayPool, One(loc_iv));
  assert Vec_Contains(vec, i);
  v := Vec_Nth(vec, i);
}
yield procedure {:layer 2} IntArray_Read({:linear} tid: One Tid, loc_iv: Loc IntArray, i: int) returns (v: int)
refines Atomic_IntArray_Read;
preserves call IntArrayDom();
preserves call Yield(loc_iv);
{
  var loc_mutex: Loc int;
  var {:linear} cell_int: Cell (Loc int) int;
  var {:linear} one_loc_int: One (Loc int);

  call loc_mutex := GetLocMutex(loc_iv, i);
  call Mutex_Acquire(tid, loc_mutex);
  call cell_int := Locked_GetOwnedLocInt(tid, loc_iv, i);
  Cell(one_loc_int, v) := cell_int;
  cell_int := Cell(one_loc_int, v);
  call Locked_PutOwnedLocInt(tid, loc_iv, i, cell_int);
  call Mutex_Release(tid, loc_mutex);
}

atomic action {:layer 3} Atomic_IntArray_Write({:linear} tid: One Tid, loc_iv: Loc IntArray, i: int, v: int)
modifies IntArrayPool;
{
  var vec: Vec int;
  assert Map_Contains(IntArrayPool, One(loc_iv));
  vec := Map_At(IntArrayPool, One(loc_iv));
  assert Vec_Contains(vec, i);
  vec := Vec_Update(vec, i, v);
  IntArrayPool := Map_Update(IntArrayPool, One(loc_iv), vec);
}
yield procedure {:layer 2} IntArray_Write({:linear} tid: One Tid, loc_iv: Loc IntArray, i: int, v: int)
refines Atomic_IntArray_Write;
preserves call IntArrayDom();
preserves call Yield(loc_iv);
{
  var loc_mutex: Loc int;
  var {:linear} cell_int: Cell (Loc int) int;
  var {:linear} one_loc_int: One (Loc int);
  var v': int;

  call loc_mutex := GetLocMutex(loc_iv, i);
  call Mutex_Acquire(tid, loc_mutex);
  call cell_int := Locked_GetOwnedLocInt(tid, loc_iv, i);
  Cell(one_loc_int, v') := cell_int;
  cell_int := Cell(one_loc_int, v);
  call Locked_PutOwnedLocInt(tid, loc_iv, i, cell_int);
  call Mutex_Release(tid, loc_mutex);
  call {:layer 2} IntArrayPool := Copy(Map_Update(IntArrayPool, One(loc_iv), Vec_Update(Map_At(IntArrayPool, One(loc_iv)), i, v)));
}

atomic action {:layer 3} Atomic_IntArray_Swap({:linear} tid: One Tid, loc_iv: Loc IntArray, i: int, j: int)
modifies IntArrayPool;
{
  var vec: Vec int;
  assert Map_Contains(IntArrayPool, One(loc_iv));
  vec := Map_At(IntArrayPool, One(loc_iv));
  assert Vec_Contains(vec, i) && Vec_Contains(vec, j);
  vec := Vec_Swap(vec, i, j);
  IntArrayPool := Map_Update(IntArrayPool, One(loc_iv), vec);
}
yield procedure {:layer 2} IntArray_Swap({:linear} tid: One Tid, loc_iv: Loc IntArray, i: int, j: int)
refines Atomic_IntArray_Swap;
preserves call IntArrayDom();
preserves call Yield(loc_iv);
{
  var i': int;
  var j': int;
  
  if (i == j) {
    return;
  }

  assert {:layer 2} Map_Contains(IntArrayPool, One(loc_iv));
  assert {:layer 2} (var vec := Map_At(IntArrayPool, One(loc_iv)); Vec_Contains(vec, i) && Vec_Contains(vec, j));

  // deadlock avoidance
  if (i < j) {
    i', j' := i, j;
  } else {
    i', j' := j, i;
  }

  call IntArray_Swap_Helper(tid, loc_iv, i', j');
  call {:layer 2} IntArrayPool := Copy(Map_Update(IntArrayPool, One(loc_iv), Vec_Swap(Map_At(IntArrayPool, One(loc_iv)), i', j')));
}

yield atomic procedure {:layer 2} IntArray_Swap_Helper({:linear} tid: One Tid, loc_iv: Loc IntArray, i: int, j: int)
requires {:layer 2} i < j;
requires {:layer 2} Map_Contains(IntArrayPoolLow, One(loc_iv));
requires {:layer 2}
  (var intArray := Map_At(IntArrayPoolLow, One(loc_iv));
    (var mutexes, values := intArray->mutexes, intArray->values;
      Map_Contains(mutexes, i) && Map_Contains(mutexes, j) && Map_Contains(values, i) && Map_Contains(values, j) && 
      Map_Contains(MutexPool, Map_At(mutexes, i)->val) && Map_Contains(MutexPool, Map_At(mutexes, j)->val)));
ensures {:layer 2}
  (var intArray := Map_At(old(IntArrayPoolLow), One(loc_iv));
    (var values := intArray->values; 
      (var cell_int_i, cell_int_j := Map_At(values, i), Map_At(values, j);
        (var values' := Map_Update(Map_Update(values, i, cell_int_j), j, cell_int_i);
          IntArrayPoolLow == Map_Update(old(IntArrayPoolLow), One(loc_iv), IntArray(intArray->mutexes, values'))))));
ensures {:layer 2} MutexPool == old(MutexPool);
{
  var loc_mutex_i: Loc int;
  var loc_mutex_j: Loc int;
  var {:linear} cell_int_i: Cell (Loc int) int;
  var {:linear} cell_int_j: Cell (Loc int) int;

  call loc_mutex_i := GetLocMutex(loc_iv, i);
  call loc_mutex_j := GetLocMutex(loc_iv, j);
  call Mutex_Acquire(tid, loc_mutex_i);
  call Mutex_Acquire(tid, loc_mutex_j);
  call cell_int_i := Locked_GetOwnedLocInt(tid, loc_iv, i);
  call cell_int_j := Locked_GetOwnedLocInt(tid, loc_iv, j);
  call Locked_PutOwnedLocInt(tid, loc_iv, i, cell_int_j);
  call Locked_PutOwnedLocInt(tid, loc_iv, j, cell_int_i);
  call Mutex_Release(tid, loc_mutex_j);
  call Mutex_Release(tid, loc_mutex_i);
} 

both action {:layer 2} Atomic_Locked_GetOwnedLocInt({:linear} tid: One Tid, loc_iv: Loc IntArray, i: int) returns ({:linear} cell_int: Cell (Loc int) int)
modifies IntArrayPoolLow;
{
  var {:linear} one_loc_iv: One (Loc IntArray);
  var {:linear} intvec: IntArray;
  var {:linear "no_collect_keys"} mutexes: Map int (One (Loc int));
  var {:linear "no_collect_keys"} values: Map int (Cell (Loc int) int);

  one_loc_iv := One(loc_iv);
  call intvec := Map_GetValue(IntArrayPoolLow, one_loc_iv);
  IntArray(mutexes, values) := intvec;

  // the following lines are added over Atomic_GetOwnedLocInt
  assert Map_Contains(MutexPool, Map_At(mutexes, i)->val);
  assert Map_At(MutexPool, Map_At(mutexes, i)->val) == Some(tid->val);

  call cell_int := Map_GetValue(values, i);
  intvec := IntArray(mutexes, values);
  call Map_PutValue(IntArrayPoolLow, one_loc_iv, intvec);
}
yield procedure {:layer 1} Locked_GetOwnedLocInt({:linear} tid: One Tid, loc_iv: Loc IntArray, i: int) returns ({:linear} cell_int: Cell (Loc int) int)
refines Atomic_Locked_GetOwnedLocInt;
{
  call cell_int := GetOwnedLocInt(loc_iv, i);
}

both action {:layer 2} Atomic_Locked_PutOwnedLocInt({:linear} tid: One Tid, loc_iv: Loc IntArray, i: int, {:linear_in} cell_int: Cell (Loc int) int)
modifies IntArrayPoolLow;
{
  var {:linear} one_loc_iv: One (Loc IntArray);
  var {:linear} intvec: IntArray;
  var {:linear "no_collect_keys"} mutexes: Map int (One (Loc int));
  var {:linear "no_collect_keys"} values: Map int (Cell (Loc int) int);

  one_loc_iv := One(loc_iv);
  call intvec := Map_GetValue(IntArrayPoolLow, one_loc_iv);
  IntArray(mutexes, values) := intvec;

  // the following lines are added over Atomic_PutOwnedLocInt
  assert Map_Contains(MutexPool, Map_At(mutexes, i)->val);
  assert Map_At(MutexPool, Map_At(mutexes, i)->val) == Some(tid->val);

  call Map_PutValue(values, i, cell_int);
  intvec := IntArray(mutexes, values);
  call Map_PutValue(IntArrayPoolLow, one_loc_iv, intvec);
}
yield procedure {:layer 1} Locked_PutOwnedLocInt({:linear} tid: One Tid, loc_iv: Loc IntArray, i: int, {:linear_in} cell_int: Cell (Loc int) int)
refines Atomic_Locked_PutOwnedLocInt;
{
  call PutOwnedLocInt(loc_iv, i, cell_int);
}

yield procedure {:layer 0} GetLocMutex(loc_iv: Loc IntArray, i: int) returns (loc_mutex: Loc int);
refines right action {:layer 1, 2} _
{
  var {:linear} one_loc_iv: One (Loc IntArray);
  var {:linear} intvec: IntArray;
  var {:linear "no_collect_keys"} mutexes: Map int (One (Loc int));
  var {:linear "no_collect_keys"} values: Map int (Cell (Loc int) int);
  var {:linear} one_loc_mutex: One (Loc int);

  one_loc_iv := One(loc_iv);
  call intvec := Map_GetValue(IntArrayPoolLow, one_loc_iv);
  IntArray(mutexes, values) := intvec;
  call one_loc_mutex := Map_GetValue(mutexes, i);
  loc_mutex := one_loc_mutex->val;
  call Map_PutValue(mutexes, i, one_loc_mutex);
  intvec := IntArray(mutexes, values);
  call Map_PutValue(IntArrayPoolLow, one_loc_iv, intvec);
}

yield procedure {:layer 0} GetOwnedLocInt(loc_iv: Loc IntArray, i: int) returns ({:linear} cell_int: Cell (Loc int) int);
refines atomic action {:layer 1, 1} _
{
  var {:linear} one_loc_iv: One (Loc IntArray);
  var {:linear} intvec: IntArray;
  var {:linear "no_collect_keys"} mutexes: Map int (One (Loc int));
  var {:linear "no_collect_keys"} values: Map int (Cell (Loc int) int);

  one_loc_iv := One(loc_iv);
  call intvec := Map_GetValue(IntArrayPoolLow, one_loc_iv);
  IntArray(mutexes, values) := intvec;
  call cell_int := Map_GetValue(values, i);
  intvec := IntArray(mutexes, values);
  call Map_PutValue(IntArrayPoolLow, one_loc_iv, intvec);
}

yield procedure {:layer 0} PutOwnedLocInt(loc_iv: Loc IntArray, i: int, {:linear_in} cell_int: Cell (Loc int) int);
refines atomic action {:layer 1, 1} _
{
  var {:linear} one_loc_iv: One (Loc IntArray);
  var {:linear} intvec: IntArray;
  var {:linear "no_collect_keys"} mutexes: Map int (One (Loc int));
  var {:linear "no_collect_keys"} values: Map int (Cell (Loc int) int);

  one_loc_iv := One(loc_iv);
  call intvec := Map_GetValue(IntArrayPoolLow, one_loc_iv);
  IntArray(mutexes, values) := intvec;
  call Map_PutValue(values, i, cell_int);
  intvec := IntArray(mutexes, values);
  call Map_PutValue(IntArrayPoolLow, one_loc_iv, intvec);
}

yield procedure {:layer 0} AddIntArrayToPool({:linear_in} one_loc_iv: One (Loc IntArray), {:linear_in} intvec: IntArray);
refines atomic action {:layer 1, 2} _
{
  call Map_PutValue(IntArrayPoolLow, one_loc_iv, intvec);
}

type Tid;
type Mutex = Option Tid;
var {:layer 0, 2} MutexPool: Map (Loc int) Mutex;

yield procedure {:layer 0} Mutex_Alloc() returns ({:linear} one_loc_l: One (Loc int));
refines right action {:layer 1, 2} _
{
  call one_loc_l := Loc_New();
  assume !Map_Contains(MutexPool, one_loc_l->val);
  MutexPool := Map_Update(MutexPool, one_loc_l->val, None());
}

yield procedure {:layer 0} Mutex_Acquire({:linear} tid: One Tid, loc_l: Loc int);
refines right action {:layer 1, 2} _
{
  assert Map_Contains(MutexPool, loc_l);
  assume Map_At(MutexPool, loc_l) == None();
  MutexPool := Map_Update(MutexPool, loc_l, Some(tid->val));
}

yield procedure {:layer 0} Mutex_Release({:linear} tid: One Tid, loc_l: Loc int);
refines left action {:layer 1, 2} _
{
  assert Map_Contains(MutexPool, loc_l);
  assert Map_At(MutexPool, loc_l) == Some(tid->val);
  MutexPool := Map_Update(MutexPool, loc_l, None());
}
