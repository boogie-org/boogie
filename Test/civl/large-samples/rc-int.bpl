// RUN: %parallel-boogie -lib:base -lib:node -timeLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type X; // type of values used in tags

datatype Counter {
    Counter(val: int, tags: UnitMap (One (Tag X)), all_tags: [One (Tag X)]bool)
}

var {:layer 0, 1} {:linear} counters: Map (One Loc) Counter;

yield invariant {:layer 1} YieldTag({:linear} tag: One (Tag X));
preserves Map_Contains(counters, One(tag->val->loc));
preserves (var counter := Map_At(counters, One(tag->val->loc)); Set_Contains(counter->all_tags, tag));

yield invariant {:layer 1} Yield();
preserves (forall loc: Loc:: Map_Contains(counters, One(loc)) ==> (var counter := Map_At(counters, One(loc)); 
            Set_IsSubset(counter->tags->dom, counter->all_tags) &&
            (forall tag: One (Tag X):: Set_Contains(counter->all_tags, tag) ==> tag->val->loc == loc)));

yield procedure {:layer 1} Allocate(val: int, xs: [X]bool) returns ({:linear} tags: UnitMap (One (Tag X)))
preserves call Yield();
{
    var one_loc: One Loc;
    var empty_map: UnitMap (One (Tag X));
    var counter: Counter;
    var all_tags: [One (Tag X)]bool;

    call one_loc, tags := Tags_New(xs);
    call empty_map := Map_MakeEmpty();
    all_tags := tags->dom;
    counter := Counter(val, empty_map, all_tags);
    call AddCounter(one_loc, counter);
}

yield procedure {:layer 1} Write({:linear} tag: One (Tag X), val: int)
preserves call Yield();
preserves call YieldTag(tag);
{
    call WriteLow(tag, val);
}

yield procedure {:layer 1} Read({:linear} tag: One (Tag X)) returns (val: int)
preserves call Yield();
preserves call YieldTag(tag);
{
    call val := ReadLow(tag);
}

yield procedure {:layer 1} Free({:linear_in} tag: One (Tag X))
preserves call Yield();
requires call YieldTag(tag);
{
    call TryRemoveCounter(tag);
}

yield procedure {:layer 0} AddCounter({:linear_in} one_loc: One Loc, {:linear_in} counter: Counter);
refines atomic action {:layer 1} _ {
    call Map_Put(counters, one_loc, counter);
}

yield procedure {:layer 0} ReadLow({:linear} tag: One (Tag X)) returns (val: int);
refines atomic action {:layer 1} _ {
    var one_loc: One Loc;

    one_loc := One(tag->val->loc);
    call val := Path_Load(counters->val[one_loc]->val);
}

yield procedure {:layer 0} WriteLow({:linear} tag: One (Tag X), val: int);
refines atomic action {:layer 1} _ {
    var one_loc: One Loc;

    one_loc := One(tag->val->loc);
    call Path_Store(counters->val[one_loc]->val, val);
}

yield procedure {:layer 0} TryRemoveCounter({:linear_in} tag: One (Tag X));
refines atomic action {:layer 1} _ {
    var one_loc: One Loc;
    var counter: Counter;
    var val: int;
    var tags: UnitMap (One (Tag X));
    var all_tags: [One (Tag X)]bool;

    one_loc := One(tag->val->loc);
    call counter := Map_Get(counters, one_loc);
    Counter(val, tags, all_tags) := counter;
    call One_Put(tags, tag);
    if (tags->dom == all_tags) {
        // do not put entry back
        return;
    }
    counter := Counter(val, tags, all_tags);
    call Map_Put(counters, one_loc, counter);
}
