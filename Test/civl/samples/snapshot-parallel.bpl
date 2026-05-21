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

yield procedure {:layer 3} main()
{
    var snapshot: [int]StampedValue;
    var i: int;
    var v: Value;

    while (*)
    invariant {:yields} {:layer 3} true;
    {
        if (*)
        {
            havoc i, v;
            call write(i, v);
        }
        else
        {
            call snapshot := scan();
        }
    }
}

yield procedure {:layer 2} scan() returns (snapshot: [int]StampedValue)
refines atomic action {:layer 3} _ {
    assume (forall j:int :: 1 <= j && j <= n  ==> snapshot[j] == mem[j]);
}
{
    var i: int;
    var b: bool;
    var r1: [int]StampedValue;
    var r2: [int]StampedValue;
    var out: StampedValue;

    while (true)
    invariant {:yields} true;
    {
        call r1 := scan_f(n);
        call r2 := scan_s(n);
        assert {:layer 2} (forall j:int :: 1 <= j && j <= n ==> (r1[j] == r2[j] ==> r1[j] == mem[j]));
        if (r1 == r2) {
            assert {:layer 2} (forall j:int :: 1 <= j && j <= n ==> r1[j] == mem[j]);
            snapshot := r1;
            break;
        }
    }
}

yield right procedure {:layer 2} scan_f(i: int) returns (snapshot: [int]StampedValue)
requires {:layer 2} 0 <= i && i <= n;
ensures {:layer 2} (forall j:int :: 1 <= j && j <= i ==>
                        snapshot[j]->ts <= mem[j]->ts &&
                        (snapshot[j]->ts == mem[j]->ts ==> snapshot[j]->value == mem[j]->value));
{
    var out: StampedValue;

    if (i == 0) {
        return;
    }
    call snapshot := scan_f(i-1) | out := read_f(i);
    snapshot[i] := out;
}

yield left procedure {:layer 2} scan_s(i: int) returns (snapshot: [int]StampedValue)
requires {:layer 2} 0 <= i && i <= n;
ensures {:layer 2} (forall j:int :: 1 <= j && j <= i ==>
                        mem[j]->ts <= snapshot[j]->ts &&
                        (snapshot[j]->ts == mem[j]->ts ==> snapshot[j]->value == mem[j]->value));
{
    var out: StampedValue;

    if (i == 0) {
        return;
    }
    call snapshot := scan_s(i-1) | out := read_s(i);
    snapshot[i] := out;
}

right action {:layer 2} action_read_f (i: int) returns (out: StampedValue)
{
    var {:pool "K"} k: int;
    var {:pool "V"} v: Value;
    
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
    var {:pool "K"} k: int;
    var {:pool "V"} v: Value;

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

yield procedure {:layer 0} write(i: int, v: Value);
refines atomic action {:layer 1,3} _ {
    mem[i] := StampedValue(mem[i]->ts + 1, v);
}

yield procedure {:layer 0} read (i: int) returns (v: StampedValue);
refines atomic action {:layer 1,3} _ {
    v := mem[i];
}