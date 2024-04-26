// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Value;

type Tid;

datatype StampedValue {
  StampedValue(ts: int, value: Value)
}

var {:layer 0,3} mem: [int]StampedValue;

const n: int;
axiom n >= 1;

atomic action {:layer 3} scan'() returns (snapshot: [int]StampedValue)
{
    assume (forall j:int :: 1 <= j && j <= n  ==> snapshot[j] == mem[j]);
}

yield procedure {:layer 2} scan() returns (snapshot: [int]StampedValue)
refines scan';
{
    var i: int;
    var b: bool;
    var r1: [int]StampedValue;
    var r2: [int]StampedValue;
    var out: StampedValue;

    while (true)
    invariant {:yields} true;
    {
        i := 1;
        while (i <= n)
        invariant {:yields} {:layer 1} true;
        invariant {:layer 2} (forall j:int :: 1 <= j && j < i ==> r1[j]->ts <= mem[j]->ts);
        invariant {:layer 2} (forall j:int :: 1 <= j && j < i ==> (r1[j]->ts == mem[j]->ts ==> r1[j]->value == mem[j]->value));
        {
            call out := read_f(i);
            r1[i] := out;
            i := i + 1; 
        }

        i := 1;
        while (i <= n)
        invariant {:yields} {:layer 1} true;
        invariant {:layer 2} (forall j:int :: 1 <= j && j < i ==> mem[j]->ts <= r2[j]->ts);
        invariant {:layer 2} (forall j:int :: 1 <= j && j < i ==> (r2[j]->ts == mem[j]->ts ==> r2[j]->value == mem[j]->value));
        {
            call out := read_s(i);
            r2[i] := out;
            i := i + 1; 
        }
   
        assert {:layer 2} (forall j:int :: 1 <= j && j <= n ==> (r1[j] == r2[j] ==> r1[j] == mem[j]));
    
        if (r1 == r2) {
            assert {:layer 2} (forall j:int :: 1 <= j && j <= n ==> r1[j] == mem[j]);
            snapshot := r1;
            break;
        }
    }
}

atomic action {:layer 2} write (v:Value, i: int)
modifies mem;
{
    var x: StampedValue;
    x := mem[i];
    mem[i] := StampedValue(x->ts + 1, v);
}

action {:layer 1} action_read (i: int) returns (v: StampedValue)
{
    v := mem[i];
}

yield procedure {:layer 0} read (i: int) returns (v: StampedValue);
refines action_read;

right action {:layer 2} action_read_f (i: int) returns (out: StampedValue)
{
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;
    if (*) {
        assume {:add_to_pool "K", mem[i]->ts, k} {:add_to_pool "V", mem[i]->value, v} true;
        assume k < mem[i]->ts;
        out := StampedValue(k, v);
    } else {
        out := mem[i];
    }
}

yield procedure {:layer 1} read_f (i: int) returns (out: StampedValue)
refines action_read_f;
{
    call out := read(i);
}

left action {:layer 2} action_read_s(i: int) returns (out: StampedValue)
{
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;

    if (*) {
        assume {:add_to_pool "K", mem[i]->ts, k} {:add_to_pool "V", mem[i]->value, v} true;
        assume k > mem[i]->ts;
        out := StampedValue(k, v);
    } else {
        out := mem[i];
    }
}

yield procedure {:layer 1} read_s (i: int) returns (out: StampedValue)
refines action_read_s;
{
    call out := read(i);
}