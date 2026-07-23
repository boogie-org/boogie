// RUN: %parallel-boogie -lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Counter {
    Counter(val: int, all_tags: [real]bool)
}

datatype Ref { Ref(loc: Loc, left: real, right: real, tags: UnitMap (One (Tag real))) }

function {:inline} RefInv(ref: Ref): bool {
    ref->left < ref->right &&
    Map_Contains(ref->tags, One(Tag(ref->loc, ref->left))) && // redundant but needed for quantifier instantiation
    (forall r: real:: ref->left <= r && r < ref->right ==> Map_Contains(ref->tags, One(Tag(ref->loc, r))))
}

function {:inline} Interval(left: real, right: real): [real]bool {
    (lambda x: real:: left <= x && x < right)
}

var {:layer 0, 1} {:linear} counters: Map (One Loc) Counter;

yield invariant {:layer 1} YieldTag({:linear} ref: Ref);
preserves RefInv(ref);
preserves Map_Contains(counters, One(ref->loc));
preserves (var counter := Map_At(counters, One(ref->loc)); Set_Contains(counter->all_tags, ref->left));

yield procedure {:layer 1} Allocate(val: int) returns ({:linear} ref: Ref)
ensures call YieldTag(ref);
{
    var one_loc: One Loc;
    var tags: UnitMap (One (Tag real));
    var counter: Counter;
    var all_tags: [real]bool;
    var xs: [real]bool;

    xs := Interval(0.0, 1.0);
    call one_loc, tags := Tags_New(xs);
    ref := Ref(one_loc->val, 0.0, 1.0, tags);
    all_tags := Set_Singleton(0.0);
    counter := Counter(val, all_tags);
    call AddCounter(one_loc, counter);
}

yield procedure {:layer 1} Write({:linear} ref: Ref, val: int)
preserves call YieldTag(ref);
{
    call WriteLow(ref, val);
}

yield procedure {:layer 1} Read({:linear} ref: Ref) returns (val: int)
preserves call YieldTag(ref);
{
    call val := ReadLow(ref);
}

yield procedure {:layer 1} Free({:linear_in} ref: Ref)
requires call YieldTag(ref);
{
    call DropReferenceCount(ref);
}

yield procedure {:layer 1} Split({:linear_in} ref: Ref) returns ({:linear} left: Ref, {:linear} right: Ref)
requires call YieldTag(ref);
ensures call YieldTag(left);
ensures call YieldTag(right);
{
    call left, right := SplitLow(ref);
}

yield procedure {:layer 0} AddCounter({:linear_in} one_loc: One Loc, {:linear_in} counter: Counter);
refines atomic action {:layer 1} _ {
    call Map_Put(counters, one_loc, counter);
}

yield procedure {:layer 0} ReadLow({:linear} ref: Ref) returns (val: int);
refines atomic action {:layer 1} _ {
    var one_loc: One Loc;

    one_loc := One(ref->loc);
    call val := Path_Load(counters->val[one_loc]->val);
}

yield procedure {:layer 0} WriteLow({:linear} ref: Ref, val: int);
refines atomic action {:layer 1} _ {
    var one_loc: One Loc;

    one_loc := One(ref->loc);
    call Path_Store(counters->val[one_loc]->val, val);
}

yield procedure {:layer 0} DropReferenceCount({:linear_in} ref: Ref);
refines atomic action {:layer 1} _ {
    var one_loc: One Loc;
    var counter: Counter;
    var val: int;
    var all_tags: [real]bool;

    one_loc := One(ref->loc);
    call counter := Map_Get(counters, one_loc);
    Counter(val, all_tags) := counter;
    all_tags := Set_Remove(all_tags, ref->left);
    if (all_tags == Set_Empty()) {
        // do not put counter back
        return;
    }
    counter := Counter(val, all_tags);
    call Map_Put(counters, one_loc, counter);
}

yield procedure {:layer 0} SplitLow({:linear_in} ref: Ref) returns ({:linear} left: Ref, {:linear} right: Ref);
refines atomic action {:layer 1} _ {
    var loc: Loc;
    var a, b, middle: real;
    var tags, left_tags, right_tags: UnitMap (One (Tag real));
    var one_loc: One Loc;
    var counter: Counter;
    var val: int;
    var all_tags: [real]bool;

    Ref(loc, a, b, tags) := ref;
    one_loc := One(loc);
    call counter := Map_Get(counters, one_loc);
    Counter(val, all_tags) := counter;
    
    middle := (a + b) / 2.0;
    all_tags := Set_Add(all_tags, middle);
    call left_tags := Map_Split(tags, Tags(loc, Interval(a, middle)));
    left := Ref(loc, a, middle, left_tags);
    call right_tags := Map_Split(tags, Tags(loc, Interval(middle, b)));
    right := Ref(loc, middle, b, right_tags);

    counter := Counter(val, all_tags);
    call Map_Put(counters, one_loc, counter);
}
