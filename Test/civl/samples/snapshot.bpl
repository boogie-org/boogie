type Value;

type Tid;

datatype StampedValue {
  StampedValue(ts: int, value: Value)
}

var {:layer 0,2} mem: [int]StampedValue;
var {:layer 0,1} r1: [Tid][int]StampedValue;
var {:layer 0,1} r2: [Tid][int]StampedValue;

const n: int;
axiom n >= 1;

atomic action {:layer 2} scan'({:linear} tid: One Tid) returns (snapshot: [int]StampedValue)
{
    assume (forall j:int :: 1 <= j && j <= n  ==> snapshot[j] == mem[j]);
}

yield procedure {:layer 1} scan({:linear} tid: One Tid) returns (snapshot: [int]StampedValue)
refines scan';
{
    var i: int;
    var b: bool;

    while (true)
    invariant {:yields} {:layer 1} true;
    {
        i := 1;
        while (i <= n)
        invariant {:layer 1} (forall j:int :: 1 <= j && j < i ==> r1[tid->val][j]->ts <= mem[j]->ts);
        invariant {:layer 1} (forall j:int :: 1 <= j && j < i ==> (r1[tid->val][j]->ts == mem[j]->ts ==> r1[tid->val][j]->value == mem[j]->value));
        {
            call read_f(tid, i);
            i := i + 1; 
        }

        i := 1;
        while (i <= n)
        invariant {:layer 1} (forall j:int :: 1 <= j && j < i ==> mem[j]->ts <= r2[tid->val][j]->ts);
        invariant {:layer 1} (forall j:int :: 1 <= j && j < i ==> (r2[tid->val][j]->ts == mem[j]->ts ==> r2[tid->val][j]->value == mem[j]->value));
        {
            call read_s(tid, i);
            i := i + 1; 
        }
   
        assert {:layer 1} (forall j:int :: 1 <= j && j <= n ==> (r1[tid->val][j] == r2[tid->val][j] ==> r1[tid->val][j] == mem[j]));
    
        call b := equality_check(tid);
        if (b) {
            assert {:layer 1} (forall j:int :: 1 <= j && j <= n ==> r1[tid->val][j] == mem[j]);
            call snapshot := read_r1(tid);
            break;
        }
    }
}

both action {:layer 1} action_equality_check({:linear} tid: One Tid) returns (b: bool)
{
    b := (forall j:int :: 1 <= j && j <= n  ==> r1[tid->val][j] == r2[tid->val][j]);
}

yield procedure {:layer 0} equality_check({:linear} tid: One Tid) returns (b: bool);
refines action_equality_check;

both action {:layer 1} action_read_r1({:linear} tid: One Tid) returns (r1_copy: [int]StampedValue)
{
    r1_copy := r1[tid->val];
}

yield procedure {:layer 0} read_r1({:linear} tid: One Tid) returns (r1_copy: [int]StampedValue);
refines action_read_r1;

atomic action {:layer 1} write ({:linear} tid: One Tid, v:Value, i: int)
modifies mem;
{
    var x: StampedValue;
    x := mem[i];
    mem[i] := StampedValue(x->ts + 1, v);
}

yield procedure {:layer 0} read_f ({:linear} tid: One Tid, i: int);
refines action_read_f;

right action {:layer 1} action_read_f ({:linear} tid: One Tid, i: int) 
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
}

yield procedure {:layer 0} read_s({:linear} tid: One Tid, i: int);
refines action_read_s;

left action {:layer 1} action_read_s({:linear} tid: One Tid, i: int)
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
}