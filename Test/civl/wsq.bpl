// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type Tid;
const nil: Tid;

function {:builtin "MapConst"} MapConstBool(bool) : [Tid]bool;
function {:inline} {:linear "tid"} TidCollector(x: Tid) : [Tid]bool
{
 MapConstBool(false)[x := true]
}



var {:layer 0,3} H: int;
var {:layer 0,3} T: int;
var {:layer 0,3} items: [int]int;
var {:layer 0,4} status: [int]bool;
var {:layer 0,3} take_in_cs: bool;
var {:layer 0,3} put_in_cs: bool;
var {:layer 0,3} steal_in_cs: [Tid]bool;
var {:layer 0,3} h_ss: [Tid]int;
var {:layer 0,3} t_ss: [Tid]int;

const IN_Q: bool;
const NOT_IN_Q: bool;
axiom IN_Q == true;
axiom NOT_IN_Q == false;

const unique EMPTY: int;
const unique NIL: Tid;
const unique ptTid: Tid;
axiom ptTid != NIL;

function {:inline} stealerTid(tid: Tid):(bool) { tid != NIL && tid != ptTid  }

function {:inline} ideasInv(put_in_cs:bool,
                           items:[int]int,
                           status: [int]bool,
                H:int, T:int,
                take_in_cs:bool,
                steal_in_cs:[Tid]bool,
                h_ss:[Tid]int,
                    t_ss:[Tid]int
                ):(bool)
{
   (
     ( (take_in_cs) && h_ss[ptTid] < t_ss[ptTid] ==> (t_ss[ptTid] == T && H <= T &&
                                                          items[T] != EMPTY && status[T] == IN_Q) ) &&
     (put_in_cs ==> !take_in_cs) && (take_in_cs ==> !put_in_cs) &&
     (( (take_in_cs) && H != h_ss[ptTid]) ==> H > h_ss[ptTid]) &&
     (forall td:Tid :: (stealerTid(td) && steal_in_cs[td] && H == h_ss[td] && H < t_ss[td]) ==> (items[H] != EMPTY && status[H] == IN_Q)) &&
     (forall td:Tid :: (stealerTid(td) && steal_in_cs[td] && H != h_ss[td]) ==> H > h_ss[td])
    )
}

function {:inline} queueInv(steal_in_cs:[Tid]bool,
                           put_in_cs:bool,
                take_in_cs:bool,
                items:[int]int, status: [int]bool, _H:int, _T:int):(bool)
{
   ( (forall i:int :: (_H <= i && i <= _T) ==> (status[i] == IN_Q && items[i] != EMPTY)) )
}

function {:inline} emptyInv(put_in_cs:bool, take_in_cs:bool, items:[int]int, status:[int]bool, T:int):(bool)
{
   (forall i:int :: (i>=T && !put_in_cs && !take_in_cs) ==> status[i] == NOT_IN_Q && items[i] == EMPTY)
}

function {:inline} putInv(items:[int]int, status: [int]bool, H:int, T:int):(bool)
{
   (forall i:int :: (H <= i && i < T) ==> (status[i] == IN_Q && items[i] != EMPTY))
}

function {:inline} takeInv(items:[int]int, status: [int]bool, H:int, T:int, t:int, h:int):(bool)
{
   (forall i:int :: (h <= i && i <= t) ==> (status[i] == IN_Q &&
    items[i] != EMPTY) &&
    t == T
   )
}

procedure {:atomic} {:layer 4} atomic_put({:linear "tid"} tid:Tid, task: int)
modifies status;
{
  var i: int;
  assume status[i] == NOT_IN_Q;
  status[i] := IN_Q;
}

procedure {:yields} {:layer 3} {:refines "atomic_put"} put({:linear "tid"} tid:Tid, task: int)
requires {:layer 3} {:expand} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && task != EMPTY && !take_in_cs && !put_in_cs;
requires {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
requires {:layer 3} {:expand} emptyInv(put_in_cs, take_in_cs, items,status,T);
ensures {:layer 3} {:expand} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
ensures {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
ensures {:layer 3} {:expand} emptyInv(put_in_cs, take_in_cs, items,status,T);
{
  var t: int;
  var {:layer 3} oldH:int;
  var {:layer 3} oldT:int;
  var {:layer 3} oldStatusT:bool;
  
  yield;
  assert {:layer 3} {:expand} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
  assert {:layer 3} {:expand} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
  assert {:layer 3} {:expand} emptyInv(put_in_cs, take_in_cs, items,status,T);

  call t := readT_put(tid);

  call oldH, oldT := GhostRead();
  yield;
  assert {:layer 3} {:expand} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && put_in_cs;
  assert {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
  assert {:layer 3} tid == ptTid && t == T;
  assert {:layer 3} oldH <= H && oldT == T;
  assert {:layer 3} (forall i:int :: i>=T ==> status[i] == NOT_IN_Q && items[i] == EMPTY);
  
  call writeItems_put(tid,t, task);

  call oldH, oldT := GhostRead();
  call oldStatusT := GhostReadStatus();
  yield;
  assert {:layer 3} {:expand} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T) && t == T && tid == ptTid && !take_in_cs && put_in_cs;
  assert {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
  assert {:layer 3} items[t] == task;
  assert {:layer 3} oldH <= H && oldT == T;
  assert {:layer 3} (forall i:int :: i>T ==> status[i] == NOT_IN_Q && items[i] == EMPTY);

  
  call writeT_put(tid, t+1);

  call oldH, oldT := GhostRead();
  yield;
  assert {:layer 3} {:expand} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
  assert {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
  assert {:layer 3} T == t + 1;
  assert {:layer 3} oldH <= H && oldT == T;
  assert {:layer 3} {:expand} emptyInv(put_in_cs, take_in_cs, items,status,T);
}

procedure {:atomic} {:layer 4} atomic_take({:linear "tid"} tid:Tid) returns (task: int, taskstatus: bool)
modifies status;
{
  var i: int;
  if (*) {
    assume status[i] == IN_Q;
    status[i] := NOT_IN_Q;
  }
}

procedure {:yields} {:layer 3} {:refines "atomic_take"} take({:linear "tid"} tid:Tid) returns (task: int, taskstatus: bool)
requires {:layer 3} {:expand} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
requires {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
ensures {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs && (task != EMPTY ==> taskstatus == IN_Q);
ensures {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
{
  var h, t: int;
  var chk: bool;
  var {:layer 3} oldH:int;
  var {:layer 3} oldT:int;

  yield;
  assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
  assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
  
  while(true)
  invariant {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
  invariant {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
  {
    call oldH, oldT := GhostRead();
    yield;
    assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
    assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} oldH <= H && oldT == T;
    
    call t := readT_take_init(tid);

    call oldH, oldT := GhostRead();
    yield;
    assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
    assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} t == T;
    assert {:layer 3} items[t-1] == EMPTY ==> H > t-1;
    assert {:layer 3} oldH <= H && oldT == T;
   
    t := t-1;
    call writeT_take(tid, t);

    call oldH, oldT := GhostRead();
    yield;
    assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T) && tid == ptTid && !take_in_cs && !put_in_cs && t_ss[tid] == t;
    assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} t == T;
    assert {:layer 3} items[t] == EMPTY ==> H > t;
    assert {:layer 3} oldH <= H && oldT == T;
   
    call h := readH_take(tid);

    call oldH, oldT := GhostRead();
    yield;
    assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T) && tid == ptTid && take_in_cs  && !put_in_cs && h_ss[tid] == h && t_ss[tid] == t;
    assert {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} t == T;
    assert {:layer 3} h <= H;
    assert {:layer 3} items[t] == EMPTY ==> H > t;
    assert {:layer 3} oldH <= H;
    assert {:layer 3} oldT == T;
    assert {:layer 3} h <= H;
    assert {:layer 3} oldH == h;

    if(t<h) {
      call writeT_take_abort(tid, h);
      task := EMPTY;

      call oldH, oldT := GhostRead();
      yield;
      assert {:layer 3} h <= H;
      assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
      assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
      assert {:layer 3} h == T;
      assert {:layer 3} oldH <= H && oldT == T;
      return;
    }

    call task, taskstatus := readItems(tid, t);

    call oldH, oldT := GhostRead();
    yield;
    assert {:layer 3} H >= h;
    assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T) && tid == ptTid && take_in_cs && h_ss[tid] == h && t_ss[tid] == t;
    assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} t == T && task == items[T];
    assert {:layer 3} T > H ==> items[T] != EMPTY;
    assert {:layer 3} oldH <= H && oldT == T && !put_in_cs && take_in_cs;

    if(t>h) {
      call takeExitCS(tid);

      call oldH, oldT := GhostRead();
      yield;
      assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && h_ss[tid] == h && t_ss[tid] == t;
      assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
      assert {:layer 3} t == T && task == items[t] && task != EMPTY && taskstatus == IN_Q;
      assert {:layer 3} oldH <= H && oldT == T && !put_in_cs && !take_in_cs;
      return;
    }
    call writeT_take_eq(tid, h+1);
    call oldH, oldT := GhostRead();
    
    yield;
    assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && h_ss[tid] == h && t_ss[tid] == t;
    assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} T == h + 1;
    assert {:layer 3} oldH <= H;
    assert {:layer 3} oldT == T;
    assert {:layer 3} task == items[t];
    assert {:layer 3} !put_in_cs;
    
    call chk := CAS_H_take(tid, h,h+1);

    call oldH, oldT := GhostRead();
    yield;
    assert {:layer 3} chk ==> (h+1 == oldH && h_ss[tid] == oldH -1 && task != EMPTY);
    assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && h_ss[tid] == h && t_ss[tid] == t;
    assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} h+1 == T;
    assert {:layer 3} task == items[t];
    assert {:layer 3} !take_in_cs;
    assert {:layer 3} !put_in_cs;
    assert {:layer 3} oldH <= H && oldT == T;

    if (chk) {
      call oldH, oldT := GhostRead();
      yield;
      assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && h_ss[tid] == h && t_ss[tid] == t;
      assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
      assert {:layer 3} h+1 == T && task == items[t] && !take_in_cs && !put_in_cs;
      assert {:layer 3} oldH <= H && oldT == T && task != EMPTY && taskstatus == IN_Q;
      return;
    }

    call oldH, oldT := GhostRead();
    yield;
    assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && h_ss[tid] == h && t_ss[tid] == t;
    assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} h+1 == T && task == items[t] && !take_in_cs && !put_in_cs;
    assert {:layer 3} oldH <= H && oldT == T;
  }
  
  call oldH, oldT := GhostRead();
  yield;
  assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T) && tid == ptTid && !put_in_cs;
  assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
  assert {:layer 3} oldH <= H && oldT == T;
}

procedure {:atomic} {:layer 4} atomic_steal({:linear "tid"} tid:Tid) returns (task: int, taskstatus: bool)
modifies status;
{
  var i: int;
  if (*) {
    assume status[i] == IN_Q;
    status[i] := NOT_IN_Q;
  }
}

procedure {:yields} {:layer 3} {:refines "atomic_steal"} steal({:linear "tid"} tid:Tid) returns (task: int, taskstatus: bool)
requires {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && stealerTid(tid) &&
                   !steal_in_cs[tid];
requires {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
ensures {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) &&
                   !steal_in_cs[tid] && (task != EMPTY ==> taskstatus == IN_Q);
ensures {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
{
  var h, t: int;
  var chk: bool;
  var {:layer 3} oldH:int;
  var {:layer 3} oldT:int;

  yield;
  assert {:layer 3} stealerTid(tid);
  assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
  assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
  assert {:layer 3} !steal_in_cs[tid];

  while(true)
  invariant {:layer 3} stealerTid(tid);
  invariant {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
  invariant {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
  invariant {:layer 3} !steal_in_cs[tid];
  {
    call oldH, oldT := GhostRead();
    yield;
    assert {:layer 3} stealerTid(tid);
    assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
    assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} oldH <= H;
    assert {:layer 3} !steal_in_cs[tid];
    
    call h := readH_steal(tid);

    call oldH, oldT := GhostRead();
    yield;
    assert {:layer 3} H >= h;
    assert {:layer 3} !steal_in_cs[tid];
    assert {:layer 3} h_ss[tid] == h;
    assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
    assert {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} oldH <= H;

    call t := readT_steal(tid);


    call oldH, oldT := GhostRead();
    yield;
    assert {:layer 3} steal_in_cs[tid];
    assert {:layer 3} stealerTid(tid) && H >= h && steal_in_cs[tid] && h_ss[tid] == h;
    assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
    assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} oldH <= H && t == t_ss[tid];
    assert {:layer 3} (h < t && take_in_cs && (h_ss[ptTid] < t_ss[ptTid]) && h == H) ==> (H < T);
    assert {:layer 3} H >= h;

    if( h>= t) {
      task := EMPTY;
      call stealExitCS(tid);

      call oldH, oldT := GhostRead();
      yield;
      assert {:layer 3} !steal_in_cs[tid];
      assert {:layer 3} stealerTid(tid) && !steal_in_cs[tid] && h_ss[tid] == h;
      assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
      assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
      assert {:layer 3} oldH <= H;
      return;
    }
    
    call task, taskstatus := readItems(tid, h);


    call oldH, oldT := GhostRead();
    yield;
    assert {:layer 3} stealerTid(tid) && steal_in_cs[tid] && h_ss[tid] == h;
    assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
    assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} oldH <= H;
    assert {:layer 3} oldH == H && H == h && h_ss[tid] == h ==> task != EMPTY;
    assert {:layer 3} (take_in_cs && (h_ss[ptTid] < t_ss[ptTid]) && h == H) ==> (H < T);
    assert {:layer 3} h == H ==> status[H] == IN_Q;

    call chk := CAS_H_steal(tid, h,h+1);

    call oldH, oldT := GhostRead();
    yield;
    assert {:layer 3} h_ss[tid] == h;
    assert {:layer 3} chk ==> (h+1 == oldH && h_ss[tid] == h && task != EMPTY && taskstatus == IN_Q);
    assert {:layer 3} (take_in_cs && (h_ss[ptTid] < t_ss[ptTid]) && chk) ==> ((oldH-1) < T);
    assert {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} stealerTid(tid) && !steal_in_cs[tid];
    assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
    assert {:layer 3} oldH <= H;

    if(chk) {
      call oldH, oldT := GhostRead();
      yield;
      assert {:layer 3} stealerTid(tid) && !steal_in_cs[tid];
      assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
      assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
      assert {:layer 3} oldH <= H && task != EMPTY;
      return;
    }
  }
   
  call oldH, oldT := GhostRead();
  yield;
  assert {:layer 3} chk && task != EMPTY;
  assert {:layer 3} stealerTid(tid) && !steal_in_cs[tid];
  assert {:layer 3} oldH <= H;
}

procedure {:layer 3} {:inline 1} GhostRead() returns (oldH: int, oldT: int)
{
  oldH := H;
  oldT := T;
}

procedure {:layer 3} {:inline 1} GhostReadStatus() returns (oldStatus: bool)
{
  oldStatus := status[T];
}

procedure {:atomic} {:layer 1,3} atomic_readH_take({:linear "tid"} tid:Tid) returns (y: int)
modifies take_in_cs, h_ss;
{ assert tid == ptTid; y := H; take_in_cs := true; h_ss[tid] := H; }

procedure {:yields} {:layer 0} {:refines "atomic_readH_take"} readH_take({:linear "tid"} tid:Tid) returns (y: int);

procedure {:atomic} {:layer 1,3} atomic_readH_steal({:linear "tid"} tid:Tid) returns (y: int)
modifies h_ss;
{ assert stealerTid(tid); assert !steal_in_cs[tid]; y := H; h_ss[tid] := H; }

procedure {:yields} {:layer 0} {:refines "atomic_readH_steal"} readH_steal({:linear "tid"} tid:Tid) returns (y: int);

procedure {:atomic} {:layer 1,3} atomic_readT_take_init({:linear "tid"} tid:Tid) returns (y: int)
{ assert tid != NIL; assert tid == ptTid; y := T; }

procedure {:yields} {:layer 0} {:refines "atomic_readT_take_init"} readT_take_init({:linear "tid"} tid:Tid) returns (y: int);

procedure {:atomic} {:layer 1,3} atomic_readT_put({:linear "tid"} tid:Tid) returns (y: int)
modifies put_in_cs;
{ assert tid != NIL; assert tid == ptTid; put_in_cs := true; y := T; }

procedure {:yields} {:layer 0} {:refines "atomic_readT_put"} readT_put({:linear "tid"} tid:Tid) returns (y: int);

procedure {:atomic} {:layer 1,3} atomic_readT_steal({:linear "tid"} tid:Tid) returns (y: int)
modifies t_ss, steal_in_cs;
{ assert tid != NIL; assert stealerTid(tid); assert !steal_in_cs[tid]; y := T; t_ss[tid] := T; steal_in_cs[tid] := true; }

procedure {:yields} {:layer 0} {:refines "atomic_readT_steal"} readT_steal({:linear "tid"} tid:Tid) returns (y: int);

procedure {:atomic} {:layer 1,3} atomic_readItems({:linear "tid"} tid:Tid, ind: int) returns (y: int, b:bool)
{ y := items[ind]; b := status[ind]; }

procedure {:yields} {:layer 0} {:refines "atomic_readItems"} readItems({:linear "tid"} tid:Tid, ind: int) returns (y: int, b:bool);

procedure {:atomic} {:layer 1,3} atomic_writeT_put({:linear "tid"} tid:Tid, val: int)
modifies T, put_in_cs;
{ assert tid == ptTid; T := T+1; put_in_cs := false; }

procedure {:yields} {:layer 0} {:refines "atomic_writeT_put"} writeT_put({:linear "tid"} tid:Tid, val: int);

procedure {:atomic} {:layer 1,3} atomic_writeT_take({:linear "tid"} tid:Tid, val: int)
modifies T, t_ss;
{ assert tid == ptTid; T := val; t_ss[tid] := val; }

procedure {:yields} {:layer 0} {:refines "atomic_writeT_take"} writeT_take({:linear "tid"} tid:Tid, val: int);

procedure {:atomic} {:layer 1,3} atomic_writeT_take_abort({:linear "tid"} tid:Tid, val: int)
modifies T, take_in_cs;
{ assert tid == ptTid; assert take_in_cs; T := val; take_in_cs := false; }

procedure {:yields} {:layer 0} {:refines "atomic_writeT_take_abort"} writeT_take_abort({:linear "tid"} tid:Tid, val: int);

procedure {:atomic} {:layer 1,3} atomic_writeT_take_eq({:linear "tid"} tid:Tid, val: int)
modifies T;
{ assert tid == ptTid; T := val; }

procedure {:yields} {:layer 0} {:refines "atomic_writeT_take_eq"} writeT_take_eq({:linear "tid"} tid:Tid, val: int);

procedure {:atomic} {:layer 1,3} atomic_takeExitCS({:linear "tid"} tid:Tid)
modifies take_in_cs;
{ assert tid == ptTid; take_in_cs := false; }

procedure {:yields} {:layer 0} {:refines "atomic_takeExitCS"} takeExitCS({:linear "tid"} tid:Tid);

procedure {:atomic} {:layer 1,3} atomic_stealExitCS({:linear "tid"} tid:Tid)
modifies steal_in_cs;
{ assert stealerTid(tid); assert steal_in_cs[tid]; steal_in_cs[tid] := false; }

procedure {:yields} {:layer 0} {:refines "atomic_stealExitCS"} stealExitCS({:linear "tid"} tid:Tid);

procedure {:atomic} {:layer 1,3} atomic_writeItems({:linear "tid"} tid:Tid, idx: int, val: int)
modifies items, status;
{ assert tid == ptTid; assert val != EMPTY; items[idx] := val; status[idx] := IN_Q; }

procedure {:yields} {:layer 0} {:refines "atomic_writeItems"} writeItems({:linear "tid"} tid:Tid, idx: int, val: int);

procedure {:atomic} {:layer 1,3} atomic_writeItems_put({:linear "tid"} tid:Tid, idx: int, val: int)
modifies items, status;
{ assert tid == ptTid; assert val != EMPTY; items[idx] := val; status[idx] := IN_Q; }

procedure {:yields} {:layer 0} {:refines "atomic_writeItems_put"} writeItems_put({:linear "tid"} tid:Tid, idx: int, val: int);

procedure {:atomic} {:layer 1,3} atomic_CAS_H_take({:linear "tid"} tid:Tid, prevVal :int, val: int) returns (result: bool)
modifies status, H, take_in_cs;
{
  assert tid == ptTid;
  if (H == prevVal) {
    status[H] := NOT_IN_Q;
    H := H+1;
    result := true;
    take_in_cs := false;
  } else {
    result := false;
    take_in_cs := false;
  }
}

procedure {:yields} {:layer 0} {:refines "atomic_CAS_H_take"} CAS_H_take({:linear "tid"} tid:Tid, prevVal :int, val: int) returns (result: bool);

procedure {:atomic} {:layer 1,3} atomic_CAS_H_steal({:linear "tid"} tid:Tid, prevVal :int, val: int) returns (result: bool)
modifies status, H, steal_in_cs;
{
  assert stealerTid(tid);
  if (H == prevVal) {
    status[H] := NOT_IN_Q;
    H := H+1;
    result := true;
    steal_in_cs[tid] := false;
  } else {
    result := false;
    steal_in_cs[tid] := false;
  }
}

procedure {:yields} {:layer 0} {:refines "atomic_CAS_H_steal"} CAS_H_steal({:linear "tid"} tid:Tid, prevVal :int, val: int) returns (result: bool);
