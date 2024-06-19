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

// permissions need to put back in globals to retry later
// how to know scan ended
// if r1 == r2, return snapshot 


// implement one iteration
// first scan, second scan 
// if it succeeds then good, otherwise nothing.



// prove that snapshot is correct if it succeeds.
// make it retryable anyway

const n: int;
axiom n >= 1;

var {:layer 0,2} mem: [int]StampedValue;
var {:layer 0,2} r1: [Tid][int]StampedValue;  
var {:layer 0,2} r2: [Tid][int]StampedValue; 
var {:linear} {:layer 0,2} pSet: Set Permission;

function {:inline} WholeTidPermission(tid: Tid): Set Permission {
  Set((lambda {:pool "DirPermission"} x: Permission :: x->t_id == tid && (1 <= x->mem_index) && (x->mem_index <= n)))
}

action start({:linear_in} tid: One Tid)
{
    call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid->val) && (1 <= x->mem_index) && (x->mem_index <= n)));
    async main_f(tid, sps); 
}


// M =  main_f , \elim = read_f, I = Inv_f, M' = main_f'
action {:layer 1} main_f({:linear_in} tid: One Tid, sps)
refines {:IS_right} main_f' using Inv_f;
modifies pSet;
creates read_f;
{
    // var {:linear} sps: Set Permission;
    assume {:add_to_pool "A", 0} true;
    // call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid->val) && (1 <= x->mem_index) && (x->mem_index <= n)));
    call create_asyncs((lambda pa:read_f :: (1 <= pa->i) && (pa->i <= n) && pa->perm == One(Permission(tid->val, pa->i))));
}

async action {:layer 1} gather_f({:linear_in} perm: One Permission)
modifies pSet;
{
    call One_Put(pSet, perm);
    // call Set_Get(pSet(lambda x: Permission :: (x->t_id == tid->val) && (1 <= x->mem_index) && (x->mem_index <= n)));
    // if (*){
    assume Set_IsSubset(WholeTidPermission(tid->val), pSet);
    // }
}

action {:layer 2} main_f'({:linear_in} tid: One Tid, )
modifies r1, pSet;
{
    var {:linear} sps: Set Permission;
    var {:linear} done_set: Set Permission;

    call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid->val) && (1 <= x->mem_index) && (x->mem_index <= n)));
    havoc r1;
    assume (forall i:int :: ((1 <= i && i <= n) ==> (r1[tid->val][i]->ts < mem[i]->ts  || r1[tid->val][i]== mem[i]))); 
    call done_set := Set_Get(sps, (lambda x: Permission :: (x->t_id == tid->val) && (1 <= x->mem_index) && (x->mem_index <= n))); 
    call Set_Put(pSet, done_set);
}

// implementation:
// 1. alpha
// 2. check right mover check only for alpha. (For now let the user provide alpha as a helper action)
// Start with this: 3. check that permission are only put in globals, not taken (for all actions) - can we do it only for eliminated actions?
// 4. inconsistency check (total D). Construct X (chi). 

// set of initial states from which an action executes successfully without blocking (chi is this without the transitions from alpha(A))

// alright this is a good place. Now let's get to work. 
// to construct chi, we take all g.l such that A succeeds (does not fail or block) - J, and then we take all g.l such that alpha(A) succeeds - I

// is J - I equal to X ? 


async action {:layer 1} {:alpha "read_f_alpha"} read_f({:linear_in} perm: One Permission, i: int)
creates read_f, gather_f;
modifies r1, pSet;
{
    // gate = 
    // var {:linear} sps2: Set Permission;
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;

    if (*) {
        assume {:add_to_pool "K", mem[i]->ts, k} {:add_to_pool "V", mem[i]->value, v} true;
        assume k < mem[i]->ts; 
        r1[perm->val->t_id][i]:= StampedValue(k, v);
    } else {
        r1[perm->val->t_id][i]:= mem[i];
    }
    // call Set_Put(pSet, Set((lambda x: Permission :: (x->t_id == perm->val->t_id) && (i == x->mem_index) )));
    call One_Put(pSet, perm);

    //case X 
    if (Set_IsSubset(WholeTidPermission(perm->val->t_id), pSet)){
        then: create async main_s
    }
    else{
        
    }
    // call sps2 = Set_Get(pSet)
    // call create_async(gather_f(perm));
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
creates read_f, gather_f;
{
    var {:pool "A"} j: int;
    var {:linear} sps: Set Permission;
    var {:linear} done_set: Set Permission;
    var choice: read_f;

    call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid->val) && (1 <= x->mem_index) && (x->mem_index <= n)));
    assume {:add_to_pool "A", j+1, 0} 0 <= j && j <= n;
    havoc r1;
    assume (forall i:int :: ((1 <= i && i <= j) ==> (r1[tid->val][i]->ts < mem[i]->ts || r1[tid->val][i]== mem[i]))); 
    call done_set := Set_Get(sps, (lambda x: Permission :: (x->t_id == tid->val) && (1 <= x->mem_index) && (x->mem_index <= j))); 
    call Set_Put(pSet, done_set);
    if (j < n){
        choice := read_f(One(Permission(tid->val, j+1)), j+1);
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C" } pa:read_f :: ((j+1) <= pa->i) && (pa->i <= n) && pa->perm == One(Permission(tid->val, pa->i))));
        call set_choice(choice);
    }
}

// // ISL part

// M =  main_s , \elim = read_s, I = Inv_s, M' = main_s'
action {:layer 1} main_s({:linear_in} tid: One Tid)
refines {:IS_left} main_s' using Inv_s;
modifies pSet;
creates read_s;
{
    var {:linear} sps: Set Permission;

    assume {:add_to_pool "A", 0} true;
    call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid->val) && (1 <= x->mem_index) && (x->mem_index <= n)));
    call create_asyncs((lambda pa:read_s :: (1 <= pa->i) && (pa->i <= n) && pa->perm == One(Permission(tid->val, pa->i))));
}

action {:layer 2} main_s'({:linear_in} tid: One Tid)
modifies r2, pSet;
{
    var {:linear} sps: Set Permission;

    call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid->val) && (1 <= x->mem_index) && (x->mem_index <= n)));
    havoc r2;
    assume (forall i:int :: ((1 <= i && i <= n) ==> (r2[tid->val][i]->ts > mem[i]->ts  || r2[tid->val][i] == mem[i]))); 
}

async action {:layer 1} read_s({:linear_in} perm: One Permission, i: int)
creates read_s;
modifies r2;
{
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;

    if (*) {
        assume {:add_to_pool "K", mem[i]->ts, k} {:add_to_pool "V", mem[i]->value, v} true;
        assume k > mem[i]->ts; 
        r2[perm->val->t_id][i] := StampedValue(k, v);
    } else {
        r2[perm->val->t_id][i] := mem[i];
    }
}

action {:layer 1} Inv_s({:linear_in} tid: One Tid)
modifies r2, pSet;
creates read_s;
{
    var {:pool "A"} j: int;
    var {:linear} sps: Set Permission;
    var choice: read_s;

    call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid->val) && (1 <= x->mem_index) && (x->mem_index <= n)));
    assume {:add_to_pool "A", j+1} 0 <= j && j <= n;
    havoc r2;
    assume (forall i:int :: ((1 <= i && i <= j) ==> (r2[tid->val][i]->ts > mem[i]->ts || r2[tid->val][i] == mem[i]))); 
    if (j < n){
        choice := read_s(One(Permission(tid->val, j+1)), j+1);
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C" } pa:read_s :: ((j+1) <= pa->i) && (pa->i <= n) && pa->perm == One(Permission(tid->val, pa->i))));
        call set_choice(choice);
    }
}