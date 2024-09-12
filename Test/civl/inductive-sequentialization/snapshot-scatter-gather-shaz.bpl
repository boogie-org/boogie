// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Value;

type Tid;

datatype StampedValue {
    StampedValue(ts: int, value: Value)
} 

datatype Permission {
    Permission(t_id: Tid, mem_index: int)
}

const n: int;
axiom n >= 1;

var {:layer 0,3} mem: [int]StampedValue;
var {:layer 0,3} r1: [Tid][int]StampedValue;  
var {:layer 0,3} r2: [Tid][int]StampedValue; 
var {:linear} {:layer 0,3} pSet: Set Permission;
var {:layer 0,3} done_first: [Tid]bool;
var {:layer 0,3} done_second: [Tid]bool; 

function {:inline} WholeTidPermission(tid: Tid): Set Permission {
    Set((lambda {:pool "D"} x: Permission :: x->t_id == tid && (1 <= x->mem_index) && (x->mem_index <= n)))
}

atomic action {: layer 1,2} write(i: int,v: Value)
modifies mem;
{
    var x: StampedValue;
    x := mem[i];
    mem[i] := StampedValue(x->ts + 1, v);
}

// atomic action {:layer 3} action_coordinator(tid: Tid)
// modifies pSet;
// {
//     // a bunch of ytoy fragments 
//     // hide done_first, done_second, r1, r2
//     // mem and pSet exist and pSet is not modified.
// }

// yield procedure {:layer 2} coordinator (tid: Tid)
// // refines action_coordinator;
// {
//     var {:linear} sps: Set Permission;
//     assume old(done_first) == false;
//     call Yield();
//     call sps := get_permissions(tid);
//     call Yield();
//     call main_f(tid, sps);
//     call Yield();
//     call check_first();
//     call Yield();
//     call sps := get_permissions(tid);
//     call Yield();
//     call main_s(tid, sps);
//     call Yield();
//     call check_second();
// }

// yield invariant {:layer 2} Yield();
// invariant true;

// action {:layer 1,3} action_get_permissions (tid: Tid) returns ({:linear} sps: Set Permission)
// modifies pSet;
// {
//     call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n)));
// }
// yield procedure {:layer 0} get_permissions (tid: Tid) returns ({:linear} sps: Set Permission);
// refines action_get_permissions;

// action {:layer 1,2} action_check_first(tid: Tid)
// {
//     assume done_first[tid];
// }
// yield procedure {:layer 0} check_first(tid: Tid);
// refines action_check_first;

// action {:layer 1,2} action_check_second(tid: Tid)
// {
//     assume done_second[tid];
// }
// yield procedure {:layer 0} check_second(tid: Tid);
// refines action_check_second;

/////////////////////////////////////////////////////////////////////////////////////////////

// async action {:layer 1,2} action_main_f(tid: Tid, {:linear_in} sps: Set Permission)
// refines {:IS_right} main_f' using Inv_f;
// creates read_f;
// {
//     assume {:add_to_pool "A", 0, n} true;
//     assert (sps == Set((lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n))));
//     call create_asyncs((lambda pa:read_f :: (1 <= pa->perm->val->mem_index) && (pa->perm->val->mem_index <= n) && pa->perm->val->t_id == tid));
// }
// yield procedure {:layer 0} main_f(tid: Tid, {:linear_in} sps: Set Permission);
// refines action_main_f;

// action {:layer 2,3} main_f'(tid: Tid, {:linear_in} sps: Set Permission)
// modifies r1, pSet, done_first;
// {
//     var {:linear} sps2: Set Permission;
//     var {:linear} done_set: Set Permission;
//     sps2 := sps;
//     assume {:add_to_pool "A", 0, n} true;
//     assert (sps == Set((lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n))));
//     havoc r1;
//     assume (forall i:int :: ((1 <= i && i <= n) ==> (r1[tid][i]->ts < mem[i]->ts  || r1[tid][i]== mem[i]))); 
//     call done_set := Set_Get(sps2, (lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n))); 
//     call Set_Put(pSet, done_set);
//     done_first[tid] := true;
// }

// async action {:layer 1,2} {:exit_condition Set_IsSubset(WholeTidPermission(perm->val->t_id), Set_Add(pSet, perm->val))} read_f({:linear_in} perm: One Permission)
// modifies r1, pSet, done_first;
// {
//     var {:pool "K"} k:int;
//     var {:pool "V"} v:Value;
//     assert 1 <= perm->val->mem_index && perm->val->mem_index <=n;
//     assume {:add_to_pool "A", 0, n} true;

//     if (*) {
//         assume {:add_to_pool "K", mem[perm->val->mem_index]->ts, k} {:add_to_pool "V", mem[perm->val->mem_index]->value, v} true;
//         assume k < mem[perm->val->mem_index]->ts; 
//         r1[perm->val->t_id][perm->val->mem_index]:= StampedValue(k, v);
//     } else {
//         r1[perm->val->t_id][perm->val->mem_index]:= mem[perm->val->mem_index];
//     }
//     call One_Put(pSet, perm);

//     if (Set_IsSubset(WholeTidPermission(perm->val->t_id), pSet)){
//         done_first[perm->val->t_id] := true;
//     }
// }

// action {:layer 1,2} Inv_f(tid: Tid, {:linear_in} sps: Set Permission)
// modifies r1, pSet, done_first;
// creates read_f;
// {
//     var {:pool "A"} j: int;
//     var {:linear} sps2: Set Permission;
//     var {:linear} done_set: Set Permission;
//     var choice: read_f;
//     sps2 := sps;
//     assert sps == WholeTidPermission(tid);
//     assume {:add_to_pool "A", 0, j+1, n} 0 <= j && j <= n;
//     havoc r1;
//     assume (forall i:int :: ((1 <= i && i <= j) ==> (r1[tid][i]->ts < mem[i]->ts || r1[tid][i]== mem[i]))); 

//     assume {:add_to_pool "D", Permission(tid, n)} true;
//     call done_set := Set_Get(sps2, (lambda {:pool "D" } x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= j)));
  
//     call Set_Put(pSet, done_set);
//     if (j < n){
//         choice := read_f(One(Permission(tid, j+1)));
//         assume {:add_to_pool "C", choice} true;
//         call create_asyncs((lambda {:pool "C" } pa:read_f :: ((j+1) <=  pa->perm->val->mem_index) && ( pa->perm->val->mem_index <= n) && pa->perm->val->t_id == tid));
//         call set_choice(choice);
//     }
//     else{
//         done_first[tid] := true;
//     }
// }
///////////////////////////////////////////////////////////////////////////////////////////////////////////


action {:layer 2,3} main_s'(tid: Tid, {:linear_in} sps: Set Permission)
modifies r2, pSet, done_second;
{
    var {:linear} sps2: Set Permission;
    var {:linear} done_set: Set Permission;
    sps2 := sps;
    assume {:add_to_pool "A", 0, n} true;
    assert (sps == Set((lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n))));
    havoc r2;
    assume (forall i:int :: ((1 <= i && i <= n) ==> (r2[tid][i]->ts > mem[i]->ts  || r2[tid][i]== mem[i]))); 
    call done_set := Set_Get(sps2, (lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n))); 
    call Set_Put(pSet, done_set);
    done_second[tid] := true;
}

async action {:layer 1,2} action_main_s(tid: Tid, {:linear_in} sps: Set Permission)
refines {:IS_left} main_s' using Inv_s;
creates read_s;
{
    assume {:add_to_pool "A", 0, n} true;
    assert (sps == Set((lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n))));
    call create_asyncs((lambda pa:read_s :: (1 <= pa->perm->val->mem_index) && (pa->perm->val->mem_index <= n) && pa->perm->val->t_id == tid));
}
yield procedure {:layer 0} main_s(tid: Tid, {:linear_in} sps: Set Permission);
refines action_main_s;

async action {:layer 1,2} {:exit_condition Set_IsSubset(WholeTidPermission(perm->val->t_id), Set_Add(pSet, perm->val))} read_s({:linear_in} perm: One Permission)
modifies r2, pSet, done_second;
{
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;
    assert 1 <= perm->val->mem_index && perm->val->mem_index <=n;
    assume {:add_to_pool "A", 0, n} true;

    if (*) {
        assume {:add_to_pool "K", mem[perm->val->mem_index]->ts, k} {:add_to_pool "V", mem[perm->val->mem_index]->value, v} true;
        assume k > mem[perm->val->mem_index]->ts; 
        r2[perm->val->t_id][perm->val->mem_index]:= StampedValue(k, v);
    } else {
        r2[perm->val->t_id][perm->val->mem_index]:= mem[perm->val->mem_index];
    }
    call One_Put(pSet, perm);

    if (Set_IsSubset(WholeTidPermission(perm->val->t_id), pSet)){
        done_second[perm->val->t_id] := true;
    }
}

action {:layer 1,2} Inv_s(tid: Tid, {:linear_in} sps: Set Permission)
modifies r2, pSet, done_second;
creates read_s;
{
    var {:pool "A"} j: int;
    var {:linear} sps2: Set Permission;
    var {:linear} done_set: Set Permission;
    var choice: read_s;
    sps2 := sps;
    assert sps == WholeTidPermission(tid);
    assume {:add_to_pool "A", 0, j+1, n} 0 <= j && j <= n;
    havoc r2;
    assume (forall i:int :: ((1 <= i && i <= j) ==> (r2[tid][i]->ts > mem[i]->ts || r2[tid][i]== mem[i]))); 

    assume {:add_to_pool "D", Permission(tid, n)} true;
    call done_set := Set_Get(sps2, (lambda {:pool "D" } x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= j)));
  
    call Set_Put(pSet, done_set);
    if (j < n){
        choice := read_s(One(Permission(tid, j+1)));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C" } pa:read_s :: ((j+1) <=  pa->perm->val->mem_index) && ( pa->perm->val->mem_index <= n) && pa->perm->val->t_id == tid));
        call set_choice(choice);
    }
    else{
        done_second[tid] := true;
    }
}