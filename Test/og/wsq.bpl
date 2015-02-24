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
var {:layer 0,3} status: [int]bool;
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
                 
procedure {:yields} {:layer 3} put({:linear "tid"} tid:Tid, task: int)
requires {:layer 3} {:expand} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && task != EMPTY && !take_in_cs && !put_in_cs;
requires {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
ensures {:layer 3} {:expand} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
ensures {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
{
   var t: int;
   var {:aux} oldH:int;
   var {:aux} oldT:int;
   var {:aux} oldStatusT:bool;
   

   oldH := H;
   oldT := T;
   yield;
   assert {:layer 3} {:expand} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
   assert {:layer 3} {:expand} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
   assert {:layer 3} oldH <= H && oldT == T;

   call t := readT_put(tid);

   oldH := H;
   oldT := T;
   yield;
   assert {:layer 3} {:expand} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && put_in_cs;
   assert {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
   assert {:layer 3} tid == ptTid && t == T;
   assert {:layer 3} oldH <= H && oldT == T;
   
   call writeItems_put(tid,t, task);

   oldH := H;
   oldT := T;
   oldStatusT := status[T];
   yield;
   assert {:layer 3} {:expand} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T) && t == T && tid == ptTid && !take_in_cs && put_in_cs;
   assert {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
   assert {:layer 3} items[t] == task;
   assert {:layer 3} oldH <= H && oldT == T;
   
   call writeT_put(tid, t+1);

   oldH := H;
   oldT := T;
   yield;
   assert {:layer 3} {:expand} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
   assert {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
   assert {:layer 3} T == t + 1;
   assert {:layer 3} oldH <= H && oldT == T;
}

procedure {:yields} {:layer 3} take({:linear "tid"} tid:Tid) returns (task: int, taskstatus: bool)
requires {:layer 3} {:expand} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
requires {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
ensures {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs && (task != EMPTY ==> taskstatus == IN_Q);
ensures {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
{
   var h, t: int;
   var chk: bool;
   var {:aux} oldH:int;
   var {:aux} oldT:int;

   oldH := H;
   oldT := T;
   yield;
   assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
   assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
   assert {:layer 3} oldH <= H && oldT == T;
   
   LOOP_ENTRY_1:

   while(true) 
   invariant {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
   invariant {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);    
   {

       oldH := H;
       oldT := T;
       yield;
       assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
    assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
       assert {:layer 3} oldH <= H && oldT == T;
    
       call t := readT_take_init(tid);

       oldH := H;
       oldT := T;
       yield;
       assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs;
       assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);    
       assert {:layer 3} t == T;
    assert {:layer 3} items[t-1] == EMPTY ==> H > t-1;
       assert {:layer 3} oldH <= H && oldT == T;
    
       t := t-1;
       call writeT_take(tid, t);

       oldH := H;
       oldT := T;
       yield;
       assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T) && tid == ptTid && !take_in_cs && !put_in_cs && t_ss[tid] == t;
       assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);    
       assert {:layer 3} t == T;
       assert {:layer 3} items[t] == EMPTY ==> H > t;
       assert {:layer 3} oldH <= H && oldT == T;
    
       call h := readH_take(tid);

       oldH := H;
       oldT := T;
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
 
           oldH := H;
           oldT := T;
           yield;
        assert {:layer 3} h <= H;
           assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && !put_in_cs; 
           assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert {:layer 3} h == T;
           assert {:layer 3} oldH <= H && oldT == T;
           return;
       }

       call task, taskstatus := readItems(tid, t);

       oldH := H;
       oldT := T;
       yield;
    assert {:layer 3} H >= h;
       assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T) && tid == ptTid && take_in_cs && h_ss[tid] == h && t_ss[tid] == t;  
       assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);    
       assert {:layer 3} t == T && task == items[T];
    assert {:layer 3} T > H ==> items[T] != EMPTY;
       assert {:layer 3} oldH <= H && oldT == T && !put_in_cs && take_in_cs;

       if(t>h) {
        call takeExitCS(tid);

           oldH := H;
           oldT := T;    
           yield;
           assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && !take_in_cs && h_ss[tid] == h && t_ss[tid] == t;  
        assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert {:layer 3} t == T && task == items[t] && task != EMPTY && taskstatus == IN_Q;
           assert {:layer 3} oldH <= H && oldT == T && !put_in_cs && !take_in_cs;
           return;
       }
	   call writeT_take_eq(tid, h+1);
	   oldH := H;
       oldT := T;
	   
	   yield;
	   assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && h_ss[tid] == h && t_ss[tid] == t;
       assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
	   assert {:layer 3} T == h + 1;
	   assert {:layer 3} oldH <= H;
	   assert {:layer 3} oldT == T;
	   assert {:layer 3} task == items[t];
	   assert {:layer 3} !put_in_cs;
	   
       call chk := CAS_H_take(tid, h,h+1);


       oldH := H;
       oldT := T;    
       yield;
	assert {:layer 3} chk ==> (h+1 == oldH && h_ss[tid] == oldH -1 && task != EMPTY);
       assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && h_ss[tid] == h && t_ss[tid] == t;  
    assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
       assert {:layer 3} h+1 == T;
	   assert {:layer 3} task == items[t];
	   assert {:layer 3} !take_in_cs;
	   assert {:layer 3} !put_in_cs;
       assert {:layer 3} oldH <= H && oldT == T;

       if(!chk) {
    
          oldH := H;
          oldT := T;    
          yield;
          assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && h_ss[tid] == h && t_ss[tid] == t;  
         assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
          assert {:layer 3} h+1 == T && task == items[t] && !take_in_cs && !put_in_cs;
          assert {:layer 3} oldH <= H && oldT == T;
   
          goto LOOP_ENTRY_1;
       }

       oldH := H;
       oldT := T;    
       yield;
       assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && tid == ptTid && h_ss[tid] == h && t_ss[tid] == t;  
    assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} h+1 == T && task == items[t] && !take_in_cs && !put_in_cs;
       assert {:layer 3} oldH <= H && oldT == T && task != EMPTY && taskstatus == IN_Q;

       return;
   }
   
   oldH := H;
   oldT := T;
   yield;
   assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T) && tid == ptTid && !put_in_cs;
   assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
   assert {:layer 3} oldH <= H && oldT == T;

}

procedure {:yields}{:layer 3} steal({:linear "tid"} tid:Tid) returns (task: int, taskstatus: bool)
requires {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) && stealerTid(tid) &&
                   !steal_in_cs[tid];
requires {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
ensures {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1) &&
                   !steal_in_cs[tid] && (task != EMPTY ==> taskstatus == IN_Q);
ensures {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
{
   var h, t: int;
   var chk: bool;
   var {:aux} oldH:int;
   var {:aux} oldT:int;

   oldH := H;
   oldT := T;
   yield;
   assert {:layer 3} stealerTid(tid);
   assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
   assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
   assert {:layer 3} oldH <= H;
   assert {:layer 3} !steal_in_cs[tid];

   LOOP_ENTRY_2:
   while(true) 
   invariant {:layer 3} stealerTid(tid);
   invariant {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
   invariant {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
   invariant {:layer 3} !steal_in_cs[tid];
   {
       oldH := H;
       oldT := T;
       yield;
    assert {:layer 3} stealerTid(tid);
       assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
       assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
       assert {:layer 3} oldH <= H;
       assert {:layer 3} !steal_in_cs[tid];
    
       call h := readH_steal(tid);

       oldH := H;
       oldT := T;
       yield;
    assert {:layer 3} H >= h;
    assert {:layer 3} !steal_in_cs[tid];
    assert {:layer 3} h_ss[tid] == h; 
       assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
       assert {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
       assert {:layer 3} oldH <= H;

       call t := readT_steal(tid);


       oldH := H;
       oldT := T;
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

           oldH := H;
           oldT := T;
           yield;
        assert {:layer 3} !steal_in_cs[tid];
        assert {:layer 3} stealerTid(tid) && !steal_in_cs[tid] && h_ss[tid] == h;
           assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
           assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
           assert {:layer 3} oldH <= H;
           return;
       }
    
       call task, taskstatus := readItems(tid, h);


       oldH := H;
       oldT := T;
       yield;
    assert {:layer 3} stealerTid(tid) && steal_in_cs[tid] && h_ss[tid] == h;
       assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
       assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
       assert {:layer 3} oldH <= H;
    assert {:layer 3} oldH == H && H == h && h_ss[tid] == h ==> task != EMPTY;
    assert {:layer 3} (take_in_cs && (h_ss[ptTid] < t_ss[ptTid]) && h == H) ==> (H < T);

       call chk := CAS_H_steal(tid, h,h+1);

       oldH := H;
       oldT := T;
       yield;
    assert {:layer 3} h_ss[tid] == h;
    assert {:layer 3} chk ==> (h+1 == oldH && h_ss[tid] == h && task != EMPTY && taskstatus == IN_Q);
    assert {:layer 3} (take_in_cs && (h_ss[ptTid] < t_ss[ptTid]) && chk) ==> ((oldH-1) < T);    
    assert {:layer 3} {:expand} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert {:layer 3} stealerTid(tid) && !steal_in_cs[tid];
       assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
       assert {:layer 3} oldH <= H;

       if(!chk) {
          goto LOOP_ENTRY_2;
       }

       oldH := H;
       oldT := T;
       yield;
    assert {:layer 3} stealerTid(tid) && !steal_in_cs[tid];
       assert {:layer 3} queueInv(steal_in_cs,put_in_cs,take_in_cs,items, status, H, T-1);
       assert {:layer 3} ideasInv(put_in_cs,items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
       assert {:layer 3} oldH <= H && task != EMPTY;
       return;
   }
   
   oldH := H;
   oldT := T;
   yield;
   assert {:layer 3} chk && task != EMPTY;
   assert {:layer 3} stealerTid(tid) && !steal_in_cs[tid];
   assert {:layer 3} oldH <= H;
}

procedure {:yields}{:layer 0,3} readH_take({:linear "tid"} tid:Tid) returns (y: int);
ensures {:atomic} |{A:  assert tid == ptTid;
                       y := H;
            take_in_cs := true;
            h_ss[tid] := H;
            return true;}|;

procedure {:yields}{:layer 0,3} readH_steal({:linear "tid"} tid:Tid) returns (y: int);
ensures {:atomic} |{A:  assert stealerTid(tid);
                       assert !steal_in_cs[tid];
                       y := H;
            h_ss[tid] := H;
            return true;}|;

procedure {:yields}{:layer 0,3} readT_take_init({:linear "tid"} tid:Tid) returns (y: int);
ensures {:atomic} |{A:  assert tid != NIL; assert tid == ptTid; y := T; return true;}|;

procedure {:yields}{:layer 0,3} readT_put({:linear "tid"} tid:Tid) returns (y: int);
ensures {:atomic} |{A:  assert tid != NIL;
                       assert tid == ptTid;
            put_in_cs := true;
            y := T;
            return true;}|;

procedure {:yields}{:layer 0,3} readT_steal({:linear "tid"} tid:Tid) returns (y: int);
ensures {:atomic} |{A:  assert tid != NIL;
                       assert stealerTid(tid);
            assert !steal_in_cs[tid];
                       y := T;
            t_ss[tid] := T;
            steal_in_cs[tid] := true;
            return true;}|;

procedure {:yields}{:layer 0,3} readItems({:linear "tid"} tid:Tid, ind: int) returns (y: int, b:bool);
ensures {:atomic} |{A: y := items[ind]; b := status[ind]; return true; }|;

procedure {:yields}{:layer 0,3} writeT_put({:linear "tid"} tid:Tid, val: int);
ensures {:atomic} |{A: assert tid == ptTid; 
                      T := T+1;
               put_in_cs := false;
                      return true; }|;

procedure {:yields}{:layer 0,3} writeT_take({:linear "tid"} tid:Tid, val: int);
ensures {:atomic} |{A: assert tid == ptTid;
                      T := val;
               t_ss[tid] := val;
                      return true; }|;

procedure {:yields}{:layer 0,3} writeT_take_abort({:linear "tid"} tid:Tid, val: int);
ensures {:atomic} |{A: assert tid == ptTid;
                      assert take_in_cs;
                      T := val;
               take_in_cs := false;
                      return true; }|;

procedure {:yields}{:layer 0,3} writeT_take_eq({:linear "tid"} tid:Tid, val: int);
ensures {:atomic} |{A: assert tid == ptTid;
                      T := val;
                      return true; }|;

procedure {:yields}{:layer 0,3} takeExitCS({:linear "tid"} tid:Tid);
ensures {:atomic} |{A: assert tid == ptTid;
               take_in_cs := false;
                      return true; }|;

procedure {:yields}{:layer 0,3} stealExitCS({:linear "tid"} tid:Tid);
ensures {:atomic} |{A: assert stealerTid(tid);
                      assert steal_in_cs[tid];
               steal_in_cs[tid] := false;
                      return true; }|;


procedure {:yields}{:layer 0,3} writeItems({:linear "tid"} tid:Tid, idx: int, val: int);
ensures {:atomic} |{A: assert tid == ptTid; 
                      assert val != EMPTY; 
                      items[idx] := val; 
                      status[idx] := IN_Q; 
                      return true; }|;


procedure {:yields}{:layer 0,3} writeItems_put({:linear "tid"} tid:Tid, idx: int, val: int);
ensures {:atomic} |{A: assert tid == ptTid; 
                      assert val != EMPTY; 
                      items[idx] := val; 
                      status[idx] := IN_Q; 
                      return true; }|;

procedure {:yields}{:layer 0,3} CAS_H_take({:linear "tid"} tid:Tid, prevVal :int, val: int)
                                          returns (result: bool);
ensures {:atomic} |{ A: assert tid == ptTid;
                       goto B, C; 
                    B: assume H == prevVal; 
                take_in_cs := false;
            status[H] := NOT_IN_Q;
            H := H+1;
            result := true;
                return true; 
                    C: assume H != prevVal; result := false; 
                take_in_cs := false;
            return true; 
}|;

procedure {:yields}{:layer 0,3} CAS_H_steal({:linear "tid"} tid:Tid, prevVal :int, val: int)
                                           returns (result: bool);
ensures {:atomic} |{ A: assert stealerTid(tid);
                       goto B, C; 
                    B: assume H == prevVal;
            status[H] := NOT_IN_Q;
                 H := H+1;
            result := true;
                steal_in_cs[tid] := false;
                return true; 
                    C: assume H != prevVal;
                result := false;
                steal_in_cs[tid] := false;
                return true; 
                 }|;