// RUN: %parallel-boogie -lib:set_size "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Role { Left(), Right() }

const N: int;
axiom 0 < N;

const Mutators: UnitMap (One (Tag Role));
axiom Mutators->dom == (lambda ticket: One (Tag Role):: ticket->val->val == Left());
axiom Set_Size(Mutators->dom) == N;

var {:layer 0,1} barrier_on: Tag bool;
var {:layer 0,1} unparked: int;
var {:layer 0,1} {:linear} parked: UnitMap (One (Tag Role));

function {:inline} LeftTicket(right: One (Tag Role)): One (Tag Role)
{
    One(Tag(right->val->loc, Left()))
}

yield procedure {:layer 0} IsBarrierOn() returns (b: bool);
refines atomic action {:layer 1} _
{
    b := barrier_on->val;
}

yield procedure {:layer 0} EnterBarrier({:linear_in} left: One (Tag Role));
refines atomic action {:layer 1} _
{
    assert left->val->val == Left();
    call One_Put(parked, left);
    unparked := unparked - 1;
}

yield procedure {:layer 0} TryLeaveBarrier({:linear} right: One (Tag Role))
    returns ({:linear} attempt: Option (One (Tag Role)));
refines atomic action {:layer 1} _
{
    var {:linear} left: One (Tag Role);

    assert right->val->val == Right();
    assert Map_Contains(parked, LeftTicket(right));
    if (barrier_on->val) {
        attempt := None();
    } else {
        left := LeftTicket(right);
        call One_Get(parked, left);
        unparked := unparked + 1;
        attempt := Some(left);
    }
}

yield procedure {:layer 0} SetBarrier(b: bool);
refines atomic action {:layer 1} _
{
    barrier_on->val := b;
}

yield procedure {:layer 0} AllParked() returns (b: bool);
refines atomic action {:layer 1} _
{
    b := unparked == 0;
}

yield invariant {:layer 1} BarrierInv();
preserves Set_IsSubset(parked->dom, Mutators->dom);
preserves Set_Size(parked->dom) + unparked == N;

yield invariant {:layer 1} MutatorInv({:linear} right: One (Tag Role));
preserves right->val->val == Right();
preserves Map_Contains(parked, LeftTicket(right));

yield invariant {:layer 1} CollectorInv({:linear} tid: One Loc, on: bool, done: bool);
preserves barrier_on == Tag(tid->val, on);
preserves done ==> on && parked == Mutators;

yield procedure {:layer 1} WaitForRelease({:linear} right: One (Tag Role))
    returns ({:linear} left: One (Tag Role))
requires call MutatorInv(right);
preserves call BarrierInv();
ensures {:layer 1} left == LeftTicket(right);
{
    var {:linear} attempt: Option (One (Tag Role));

    call attempt := TryLeaveBarrier(right);
    if (attempt is Some) {
        Some(left) := attempt;
    } else {
        call BarrierInv() | MutatorInv(right);
        call left := WaitForRelease(right);
    }
}

yield procedure {:layer 1} Mutator({:linear_in} initial_left: One (Tag Role), {:linear} right: One (Tag Role))
requires {:layer 1} right->val->val == Right() && initial_left == LeftTicket(right);
preserves call BarrierInv();
{
    var b: bool;
    var {:linear} left: One (Tag Role);

    left := initial_left;

    while (true)
        invariant {:yields} true;
        invariant call BarrierInv();
        invariant {:layer 1} right->val->val == Right() && left == LeftTicket(right);
    {
        call b := IsBarrierOn();
        if (b) {
            call BarrierInv();
            call EnterBarrier(left);
            call BarrierInv() | MutatorInv(right);
            call left := WaitForRelease(right);
        }
        // access memory here
    }
}

yield procedure {:layer 1} WaitForAllParked({:linear} tid: One Loc)
requires call CollectorInv(tid, true, false);
preserves call BarrierInv();
ensures call CollectorInv(tid, true, true);
{
    var done: bool;

    while (true)
        invariant {:yields} true;
        invariant call BarrierInv();
        invariant call CollectorInv(tid, true, false);
    {
        call done := AllParked();
        if (done) {
            call {:layer 1} Lemma_SetSize_Subset(parked->dom, Mutators->dom);
            return;
        }
    }
}

yield procedure {:layer 1} Collector({:linear} tid: One Loc)
preserves call BarrierInv();
requires call CollectorInv(tid, false, false);
{
    while (true)
        invariant {:yields} true;
        invariant call BarrierInv();
        invariant call CollectorInv(tid, false, false);
    {
        call SetBarrier(true);
        call BarrierInv() | CollectorInv(tid, true, false);
        call WaitForAllParked(tid);
        assert {:layer 1} Set_Size(parked->dom) == N;
        call SetBarrier(false);
    }
}

yield procedure {:layer 1} CreateMutators(n: int)
preserves call BarrierInv();
{
    var roles: [Role]bool;
    var {:linear} new_one_loc: One Loc;
    var {:linear} slots: UnitMap (One (Tag Role));
    var {:linear} left: One (Tag Role);
    var {:linear} right: One (Tag Role);

    if (n > 0) {
        roles := Set_Empty();
        roles := Set_Add(roles, Left());
        roles := Set_Add(roles, Right());
        call new_one_loc, slots := Tags_New(roles);
        left := One(Tag(new_one_loc->val, Left()));
        right := One(Tag(new_one_loc->val, Right()));
        call One_Get(slots, left);
        call One_Get(slots, right);
        async call Mutator(left, right);
        call CreateMutators(n - 1);
    }
}
