type Value;

type Tid;

datatype StampedValue {
  StampedValue(ts: int, value: Value)
} 

const n: int;
axiom n >= 1;


var {:layer 0,2} mem: [int]StampedValue;
var {:layer 0,2} r1: [Tid][int]StampedValue; 


// M =  main_s , \elim = read_s, I = Inv, M' = main_s'
action {:layer 1} main_f({:linear_in} tid: One Tid)
refines {:IS2_right} main_f' using right_Inv;
creates read_f;
{
    assume {:add_to_pool "A", 0} true;
    call create_async(read_f(tid, 1));
}

action {:layer 2} main_f'({:linear_in} tid: One Tid)
modifies r1;
{
    havoc r1;
    assume (forall i:int :: ((1 <= i  && i <= n) ==> (mem[i]->ts > r1[tid->val][i]->ts || r1[tid->val][i] == mem[i])));
}

async atomic action {:layer 1} read_f({:linear_in} tid: One Tid, i: int)
creates read_f;
modifies r1;
{
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;
    if (*) {
        assume {:add_to_pool "K", mem[i]->ts, k} {:add_to_pool "V", mem[i]->value, v} true;
        assume k < mem[i]->ts; 
        r1[tid->val][i] := StampedValue(k, v);
    } else {
        r1[tid->val][i] := mem[i];
    }

    if (i != n) {
        call create_async(read_f(tid, i+1));
    } 
}

atomic action {: layer 1,2} write(i: int,v: Value)
modifies mem;
{
    var x: StampedValue;
    x := mem[i];
    mem[i] := StampedValue(x->ts + 1, v);
}

action {:layer 1} right_Inv({:linear_in} tid: One Tid)
modifies r1;
creates read_f;
{
    
    var {:pool "A"} j: int;
    assume {:add_to_pool "A", j+1} 0 <= j && j <= n;
    havoc r1;
    assume (forall i:int :: ((1 <= i && i <= j) ==> (mem[i]->ts > r1[tid->val][i]->ts || r1[tid->val][i] == mem[i])));
    if (j < n) {
        call create_async(read_f(tid, j+1));
        call set_choice(read_f(tid, j+1));
    }
}