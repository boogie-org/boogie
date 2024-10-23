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

var {:layer 0,2} mem: [int]StampedValue;
var {:layer 0,2} r1: [Tid][int]StampedValue;  
var {:linear} {:layer 0,2} pSet: Set Permission;

// M =  main_f , \elim = read_f, I = Inv_f, M' = main_f'
action {:layer 1} main_f({:linear_in} tid: One Tid)
refines {:IS_right} main_f' using Inv_f;
modifies pSet;
creates read_f;
{
    var {:linear} sps: Set Permission;

    assume {:add_to_pool "A", 0} true;
    call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid->val) && (1 <= x->mem_index) && (x->mem_index <= n)));
    call create_asyncs((lambda pa:read_f :: (1 <= pa->i) && (pa->i <= n) && pa->perm == One(Permission(tid->val, pa->i))));
}

action {:layer 2} main_f'({:linear_in} tid: One Tid)
modifies r1, pSet;
{
    var {:linear} sps: Set Permission;

    call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid->val) && (1 <= x->mem_index) && (x->mem_index <= n)));
    havoc r1;
    assume (forall i:int :: ((1 <= i && i <= n) ==> (r1[tid->val][i]->ts < mem[i]->ts  || r1[tid->val][i] == mem[i]))); 
}

async action {:layer 1} read_f({:linear_in} perm: One Permission, i: int)
creates read_f;
modifies r1;
{
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;

    if (*) {
        assume {:add_to_pool "K", mem[i]->ts, k} {:add_to_pool "V", mem[i]->value, v} true;
        assume k < mem[i]->ts; 
        r1[perm->val->t_id][i] := StampedValue(k, v);
    } else {
        r1[perm->val->t_id][i] := mem[i];
    }
}

atomic action {: layer 1,2} write(i: int,v: Value)
modifies mem;
{
    var x: StampedValue;

    x := mem[i];
    mem[i] := StampedValue(x->ts + 1, v);
}

action {:layer 1} Inv_f({:linear_in} tid: One Tid)
modifies r1, pSet;
creates read_f;
{
    var {:pool "A"} j: int;
    var {:linear} sps: Set Permission;
    var choice: read_f;

    call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid->val) && (1 <= x->mem_index) && (x->mem_index <= n)));
    assume {:add_to_pool "A", j+1} 0 <= j && j <= n;
    havoc r1;
    assume (forall i:int :: ((1 <= i && i <= j) ==> (r1[tid->val][i]->ts < mem[i]->ts || r1[tid->val][i] == mem[i]))); 
    if (j < n){
        choice := read_f(One(Permission(tid->val, j+1)), j+1);
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C" } pa:read_f :: ((j+1) <= pa->i) && (pa->i <= n) && pa->perm == One(Permission(tid->val, pa->i))));
        call set_choice(choice);
    }
}