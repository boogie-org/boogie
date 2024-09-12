// RUN: %parallel-boogie "%s" > "%t"

// RUN: %diff "%s.expect" "%t"
type Value;

type Tid;

datatype StampedValue {
    StampedValue(ts: int, value: Value)
} 

datatype Permission {
    Permission(tid: Tid, mem_index: int)
}

const n: int;
axiom n >= 1;

var {:layer 0,2} mem: [int]StampedValue;
var {:linear} {:layer 0,2} pSet: Set Permission;
var {:layer 0,2} channel: [Tid](Option [int]StampedValue);
// var {:layer 0,2} channel: [Tid](Option [int]StampedValue);
var {:layer 0,1} snapshots: [Tid][int]StampedValue;  

function {:inline} WholeTidPermission(tid: Tid): Set Permission {
    Set((lambda {:pool "D"} x: Permission :: x->tid == tid && (1 <= x->mem_index) && (x->mem_index <= n)))
}

yield procedure {:layer 2} coordinator (tid: Tid)
// refines action_coordinator;
{
    // while(true){
    var {:linear} sps: Set Permission;
    // assume old(done_first) == false;
    // call Yield();
    call sps := get_permissions(tid);
    // call Yield();
    // call main_f(tid, sps); 
    // call Yield();
    // call check_first();
    // call Yield();
    // call sps := get_permissions(tid);
    // call Yield();
    // call main_s(tid, sps);
    // call Yield();
    // call check_second();
    //  assert r1 == r2 r1 == mem;
    // compare both : return snapshot
   
    // }
}


action {:layer 1,2} action_get_permissions (tid: Tid) returns ({:linear} sps: Set Permission)
modifies pSet;
{
    call sps := Set_Get(pSet, (lambda x: Permission :: (x->tid == tid) && (1 <= x->mem_index) && (x->mem_index <= n)));
}
yield procedure {:layer 0} get_permissions (tid: Tid) returns ({:linear} sps: Set Permission);
refines action_get_permissions;


atomic action {: layer 1,2} write(i: int,v: Value)
modifies mem;
{
    var x: StampedValue;
    x := mem[i];
    mem[i] := StampedValue(x->ts + 1, v);
}
/////////////////////////////////////////////////////////////////////////////////////////////

async action {:layer 1} main_f(tid: Tid, {:linear_in} sps: Set Permission)
refines {:IS_right} main_f' using Inv_f;
modifies pSet;
creates read_f;
{
    assume {:add_to_pool "A", 0, n} true;
    assert sps == WholeTidPermission(tid);
    assert channel[tid] == None();
    call create_asyncs((lambda pa:read_f :: (1 <= pa->perm->val->mem_index) && (pa->perm->val->mem_index <= n) && pa->perm->val->tid == tid));
}

async action {:layer 2} main_f'(tid: Tid, {:linear_in} sps: Set Permission)
modifies  pSet, channel;
{
    var snapshot: [int]StampedValue; 
    assume {:add_to_pool "A", 0, n} true;
    assert sps == WholeTidPermission(tid);
    assert channel[tid] == None();
    assume (forall i:int :: 1 <= i && i <= n ==> (snapshot[i]->ts < mem[i]->ts  || snapshot[i]== mem[i]));
    call Set_Put(pSet, sps);
    assert Set_IsSubset(WholeTidPermission(tid), pSet);
    assert channel[tid] == None();
    channel[tid] := Some(snapshot);
}

async action {:layer 1} {:exit_condition Set_IsSubset(WholeTidPermission(perm->val->tid), Set_Add(pSet, perm->val))} read_f({:linear_in} perm: One Permission)
modifies snapshots, pSet, channel;
{
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;
    assert 1 <= perm->val->mem_index && perm->val->mem_index <=n;
    assert channel[perm->val->tid] == None();
    assume {:add_to_pool "A", 0, n} true;
    if (*) {
        assume {:add_to_pool "K", mem[perm->val->mem_index]->ts, k} {:add_to_pool "V", mem[perm->val->mem_index]->value, v} true;
        assume k < mem[perm->val->mem_index]->ts; 
        snapshots[perm->val->tid][perm->val->mem_index]:= StampedValue(k, v);
    } else {
        snapshots[perm->val->tid][perm->val->mem_index]:= mem[perm->val->mem_index];
    }
    call One_Put(pSet, perm);
    if (Set_IsSubset(WholeTidPermission(perm->val->tid), pSet)){
            assert Set_IsSubset(WholeTidPermission(perm->val->tid), pSet);
            assert channel[perm->val->tid] == None();
            channel[perm->val->tid] := Some(snapshots[perm->val->tid]);
    }
}

action {:layer 1} Inv_f(tid: Tid, {:linear_in} sps: Set Permission)
modifies snapshots, pSet, channel;
creates read_f;
{
    var {:pool "A"} j: int;
    var {:linear} sps': Set Permission;
    var {:linear} done_set: Set Permission;
    var choice: read_f;
    assert sps == WholeTidPermission(tid);
    assert channel[tid] == None();
    assume {:add_to_pool "A", 0, j+1, n} 0 <= j && j <= n;
    havoc snapshots;
    assume (forall i:int :: ((1 <= i && i <= j) ==> (snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i]== mem[i]))); 
    assume {:add_to_pool "D", Permission(tid, n)} true;
    sps' := sps;
    call done_set := Set_Get(sps', (lambda {:pool "D" } x: Permission :: (x->tid == tid) && (1 <= x->mem_index) && (x->mem_index <= j)));
    call Set_Put(pSet, done_set);
    if (j < n){
        choice := read_f(One(Permission(tid, j+1)));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C" } pa:read_f :: ((j+1) <=  pa->perm->val->mem_index) && ( pa->perm->val->mem_index <= n) && pa->perm->val->tid == tid));
        call set_choice(choice);
    }
    else{
         assert Set_IsSubset(WholeTidPermission(tid), pSet);
         assert channel[tid] == None();
         channel[tid] := Some(snapshots[tid]);
    }
}

/////////////////////////////////////////////////////////////////////////////////////////////

async action {:layer 1} main_s(tid: Tid, {:linear_in} sps: Set Permission)
refines {:IS_left} main_s' using Inv_s;
modifies pSet;
creates read_s;
{
    assume {:add_to_pool "A", 0, n} true;
    assert sps == WholeTidPermission(tid);
    assert channel[tid] == None();
    call create_asyncs((lambda pa:read_s :: (1 <= pa->perm->val->mem_index) && (pa->perm->val->mem_index <= n) && pa->perm->val->tid == tid));
}

async action {:layer 2} main_s'(tid: Tid, {:linear_in} sps: Set Permission)
modifies  pSet, channel;
{
    var snapshot: [int]StampedValue; 
    assume {:add_to_pool "A", 0, n} true;
    assert sps == WholeTidPermission(tid);
    assert channel[tid] == None();
    assume (forall i:int :: 1 <= i && i <= n ==> (snapshot[i]->ts > mem[i]->ts  || snapshot[i]== mem[i]));
    call Set_Put(pSet, sps);
    assert Set_IsSubset(WholeTidPermission(tid), pSet);
    assert channel[tid] == None();
    channel[tid] := Some(snapshot);
}

async left action {:layer 1} read_s({:linear_in} perm: One Permission)
modifies snapshots, pSet, channel;
{
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;
    assert 1 <= perm->val->mem_index && perm->val->mem_index <=n;
    assert channel[perm->val->tid] == None();
    assume {:add_to_pool "A", 0, n} true;
    if (*) {
        assume {:add_to_pool "K", mem[perm->val->mem_index]->ts, k} {:add_to_pool "V", mem[perm->val->mem_index]->value, v} true;
        assume k > mem[perm->val->mem_index]->ts; 
        snapshots[perm->val->tid][perm->val->mem_index]:= StampedValue(k, v);
    } else {
        snapshots[perm->val->tid][perm->val->mem_index]:= mem[perm->val->mem_index];
    }
    call One_Put(pSet, perm);
    if (Set_IsSubset(WholeTidPermission(perm->val->tid), pSet)){
            assert Set_IsSubset(WholeTidPermission(perm->val->tid), pSet);
            assert channel[perm->val->tid] == None();
            channel[perm->val->tid] := Some(snapshots[perm->val->tid]);
    }
}

action {:layer 1} Inv_s(tid: Tid, {:linear_in} sps: Set Permission)
modifies snapshots, pSet, channel;
creates read_s;
{
    var {:pool "A"} j: int;
    var {:linear} sps': Set Permission;
    var {:linear} done_set: Set Permission;
    var choice: read_s;
    assert sps == WholeTidPermission(tid);
    assert channel[tid] == None();
    assume {:add_to_pool "A", 0, j+1, n} 0 <= j && j <= n;
    havoc snapshots;
    assume (forall i:int :: ((1 <= i && i <= j) ==> (snapshots[tid][i]->ts > mem[i]->ts || snapshots[tid][i]== mem[i]))); 
    assume {:add_to_pool "D", Permission(tid, n)} true;
    sps' := sps;
    call done_set := Set_Get(sps', (lambda {:pool "D" } x: Permission :: (x->tid == tid) && (1 <= x->mem_index) && (x->mem_index <= j)));
    call Set_Put(pSet, done_set);
    if (j < n){
        choice := read_s(One(Permission(tid, j+1)));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C" } pa:read_s :: ((j+1) <=  pa->perm->val->mem_index) && ( pa->perm->val->mem_index <= n) && pa->perm->val->tid == tid));
        call set_choice(choice);
    }
    else{
         assert Set_IsSubset(WholeTidPermission(tid), pSet);
         assert channel[tid] == None();
         channel[tid] := Some(snapshots[tid]);
    }
}