type Value;

type Tid;

datatype StampedValue {
  StampedValue(ts: int, value: Value)
} 

const n: int;
axiom n >= 1;

var {:layer 0,2} mem: [int]StampedValue;
var {:layer 0,2} r1: [Tid][int]StampedValue;  
var {:layer 0,2} gather1: [Tid][int]bool;
var {:layer 0,2} r2: [Tid][int]StampedValue;  
var {:layer 0,2} gather2: [Tid][int]bool;
var {:layer 0,3} snapshot: [Tid][int]StampedValue;

// M =  main_f , \elim = read_f, I = Inv, M' = main_f'
action {:layer 1} main_f({:linear_in}tid: One Tid)
refines {:IS_right} main_f' using Inv_f;
creates read_f;
{
    i := 0;
    while(i <= n){
        call create_async(read_f(tid, i));
        i := i + 1;
    }
}

action {:layer 2} main_f'({:linear_in} tid: One Tid)
modifies r1;
{
    havoc r1;
    assume (forall i:int :: ((1 <= i  && i <= n) ==> (mem[i]->ts > r1[tid->val][i]->ts || r1[tid->val][i] == mem[i])));
    var j := 0;
    while(j <= n){
        call create_async(gather_f(tid, j));
        j := j + 1;
    }
}

async action {:layer 1} read_f({:linear_in} tid: One Tid, i: int)
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
    call create_async(gather_f(tid, i));
}

async action gather_f({:linear_in} tid: One Tid, i: int){
   gather1[tid][i] = true;
   if(gather1[tid][1..n] == true){
       call create_async(main_s(tid));
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
modifies r1;
creates read_f;
{

    havoc r1;
    assume (forall i:int :: ((1 <= i && i <= j) ==> (mem[i]->ts > r1[tid->val][i]->ts || r1[tid->val][i] == mem[i])));
    while (j < n) {
        call create_async(read_f(tid, j+1));
        j := j + 1;
    }
    call set_choice(read_f(tid, j+1));
}


////////


// M =  main_s , \elim = read_s, I = Inv, M' = main_s'
action {:layer 1} main_s({:linear_in}tid: One Tid)
refines {:IS_right} main_s' using Inv_s;
creates read_s;
{
    i := 0;
    while(i <= n){
        call create_async(read_s(tid, i));
        i := i + 1;
    }
}

action {:layer 2} main_s'({:linear_in} tid: One Tid)
modifies r2;
{
    havoc r2;
    assume (forall i:int :: ((1 <= i  && i <= n) ==> (mem[i]->ts < r2[tid->val][i]->ts || r2[tid->val][i] == mem[i])));
    var j := 0;
    while(j <= n){
        call create_async(gather_s(tid, j));
        j := j + 1;
    }
}

async left action {:layer 1} read_s({:linear_in} tid: One Tid, i: int)
creates read_s;
modifies r2;
{
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;
    if (*) {
        assume {:add_to_pool "K", mem[i]->ts, k} {:add_to_pool "V", mem[i]->value, v} true;
        assume k > mem[i]->ts; 
        r2[tid->val][i] := StampedValue(k, v);
    } else {
        r2[tid->val][i] := mem[i];
    }
    call create_async(gather_s(tid, i));
}

async action gather_s({:linear_in} tid: One Tid, i: int){
   gather2[tid][i] = true;
   if(gather2[tid][1..n] == true){
      if (r1 != r2){
          gather1[tid][1..n] = false;
          gather2[tid][1..n] = false;
          call create_async(main_f(tid));
      }
      else{
        snapshot[tid] = r1[tid];
      }
   }
}

atomic action {: layer 1,2} write(i: int,v: Value)
modifies mem;
{
    var x: StampedValue;
    x := mem[i];
    mem[i] := StampedValue(x->ts + 1, v);
}

action {:layer 1} Inv_s({:linear_in} tid: One Tid)
modifies r2;
creates read_s;
{

    havoc r2;
    assume (forall i:int :: ((1 <= i && i <= j) ==> (mem[i]->ts < r2[tid->val][i]->ts || r2[tid->val][i] == mem[i])));
    while (j < n) {
        call create_async(read_s(tid, j+1));
        j := j + 1;
    }
    call set_choice(read_s(tid, j+1));
}


