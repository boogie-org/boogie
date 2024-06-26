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
var {:layer 0,2} r1: [Tid][int]StampedValue;  
var {:linear} {:layer 0,2} pSet: Set Permission;
var {:layer 0,2} channels: [Tid](Option [int]StampedValue);

function {:inline} WholeTidPermission(tid: Tid): Set Permission {
    Set((lambda {:pool "D"} x: Permission :: x->tid == tid && (1 <= x->mem_index) && (x->mem_index <= n)))
}

async action {:layer 1} main_f(tid: Tid, {:linear_in} sps: Set Permission)
refines {:IS_right} main_f' using Inv_f;
modifies pSet;
creates read_f;
{
    assume {:add_to_pool "A", 0, n} true;
    assert sps == WholeTidPermission(tid);
    assert channels[tid] == None();
    call create_asyncs((lambda pa:read_f :: (1 <= pa->perm->val->mem_index) && (pa->perm->val->mem_index <= n) && pa->perm->val->tid == tid));
}

action {:layer 2} main_f'(tid: Tid, {:linear_in} sps: Set Permission)
modifies r1, pSet, channels;
{
    var {:linear} done_set: Set Permission;
    assume {:add_to_pool "A", 0, n} true;
    assert sps == WholeTidPermission(tid);
    assert channels[tid] == None();
    havoc r1;
    assume (forall i:int :: ((1 <= i && i <= n) ==> (r1[tid][i]->ts < mem[i]->ts  || r1[tid][i]== mem[i]))); 
    call Set_Put(pSet, sps);
    call ChannelSend(tid);
}

async action {:layer 1} {:exit_condition Set_IsSubset(WholeTidPermission(perm->val->tid), Set_Add(pSet, perm->val))} read_f({:linear_in} perm: One Permission)
modifies r1, pSet, channels;
{
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;
    assert 1 <= perm->val->mem_index && perm->val->mem_index <=n;
    assume {:add_to_pool "A", 0, n} true;

    if (*) {
        assume {:add_to_pool "K", mem[perm->val->mem_index]->ts, k} {:add_to_pool "V", mem[perm->val->mem_index]->value, v} true;
        assume k < mem[perm->val->mem_index]->ts; 
        r1[perm->val->tid][perm->val->mem_index]:= StampedValue(k, v);
    } else {
        r1[perm->val->tid][perm->val->mem_index]:= mem[perm->val->mem_index];
    }
    call One_Put(pSet, perm);

    if (Set_IsSubset(WholeTidPermission(perm->val->tid), pSet)) {
        call ChannelSend(perm->val->tid);
    }
}

atomic action {:layer 1,2} write(i: int,v: Value)
modifies mem;
{
    var x: StampedValue;
    x := mem[i];
    mem[i] := StampedValue(x->ts + 1, v);
}

action {:layer 1} Inv_f(tid: Tid, {:linear_in} sps: Set Permission)
modifies r1, pSet, channels;
creates read_f;
{
    var {:pool "A"} j: int;
    var {:linear} sps2: Set Permission;
    var {:linear} done_set: Set Permission;
    var choice: read_f;
    sps2 := sps;
    assert sps == WholeTidPermission(tid);
    assert channels[tid] == None();
    assume {:add_to_pool "A", 0, j+1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i:int :: ((1 <= i && i <= j) ==> (r1[tid][i]->ts < mem[i]->ts || r1[tid][i]== mem[i]))); 

    assume {:add_to_pool "D", Permission(tid, n)} true;
    call done_set := Set_Get(sps2, (lambda {:pool "D" } x: Permission :: (x->tid == tid) && (1 <= x->mem_index) && (x->mem_index <= j)));
  
    call Set_Put(pSet, done_set);
    if (j < n) {
        choice := read_f(One(Permission(tid, j+1)));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C" } pa:read_f :: j+1 <=  pa->perm->val->mem_index && pa->perm->val->mem_index <= n && pa->perm->val->tid == tid));
        call set_choice(choice);
    } else {
        call ChannelSend(tid);
    }
}

action {:layer 1,2} ChannelSend(tid: Tid)
modifies channels;
{
    assert Set_IsSubset(WholeTidPermission(tid), pSet);
    assert channels[tid] == None();
    channels[tid] := Some(r1[tid]);
}

action {:layer 1,2} ChannelReceive(tid: Tid) returns (r: [int]StampedValue)
modifies channels;
{
    assert Set_IsSubset(WholeTidPermission(tid), pSet);
    assert channels[tid] != None();
    r := channels[tid]->t;
    channels[tid] := None();
}