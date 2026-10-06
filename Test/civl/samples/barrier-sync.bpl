// RUN: %parallel-boogie -lib:set_size "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Role { Left(), Right() }

var {:layer 0,1} barrier_on: Tag bool;
var {:layer 0,1} unparked: int;
var {:layer 0,1} {:linear} parked: UnitMap (One (Tag Role));
var {:layer 0,1} {:linear} Mutators: UnitMap (One Loc);

function {:inline} LeftTicket(right: One (Tag Role)): One (Tag Role)
{
    One(Tag(right->val->loc, Left()))
}

function {:inline} LeftTickets(one_locs: [One Loc]bool): [One (Tag Role)]bool {
    (lambda ticket: One (Tag Role):: Set_Contains(one_locs, One(ticket->val->loc)) && ticket->val->val == Left())
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

yield procedure {:layer 0} AddMutator({:linear_in} one_loc: One Loc);
refines atomic action {:layer 1} _
{
    unparked := unparked + 1;
    call One_Put(Mutators, one_loc);
}

yield invariant {:layer 1} BarrierInv();
preserves Set_Size(parked->dom) + unparked == Set_Size((Mutators->dom));
preserves (forall ticket: One (Tag Role)::
            Map_Contains(parked, ticket) ==> Map_Contains(Mutators, One(ticket->val->loc)) && ticket->val->val == Left());

yield invariant {:layer 1} MutatorInv({:linear} right: One (Tag Role), in_barrier: bool);
preserves right->val->val == Right();
preserves Map_Contains(Mutators, One(right->val->loc));
preserves in_barrier ==> Map_Contains(parked, LeftTicket(right));

yield invariant {:layer 1} CollectorInv({:linear} tid: One Loc, on: bool, done: bool);
preserves barrier_on == Tag(tid->val, on);
preserves done ==> on && (forall one_loc: One Loc:: Map_Contains(Mutators, one_loc) ==> Map_Contains(parked, One(Tag(one_loc->val, Left()))));

yield procedure {:layer 1} WaitForRelease({:linear} right: One (Tag Role))
    returns ({:linear} left: One (Tag Role))
requires call MutatorInv(right, true);
ensures call MutatorInv(right, false);
preserves call BarrierInv();
ensures {:layer 1} left == LeftTicket(right);
{
    var {:linear} attempt: Option (One (Tag Role));

    call attempt := TryLeaveBarrier(right);
    if (attempt is Some) {
        Some(left) := attempt;
    } else {
        call BarrierInv() | MutatorInv(right, true);
        call left := WaitForRelease(right);
    }
}

yield procedure {:layer 1} Mutator({:linear_in} initial_left: One (Tag Role), {:linear} right: One (Tag Role))
requires {:layer 1} right->val->val == Right() && initial_left == LeftTicket(right);
preserves call BarrierInv();
requires call MutatorInv(right, false);
{
    var b: bool;
    var {:linear} left: One (Tag Role);

    left := initial_left;

    while (true)
        invariant {:yields} true;
        invariant call BarrierInv();
        invariant call MutatorInv(right, false);
        invariant {:layer 1} right->val->val == Right() && left == LeftTicket(right);
    {
        call b := IsBarrierOn();
        if (b) {
            call BarrierInv() | MutatorInv(right, false);
            call EnterBarrier(left);
            call BarrierInv() | MutatorInv(right, true);
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
            call {:layer 1} Assume(Set_Size(Mutators->dom) == Set_Size(LeftTickets(Mutators->dom)));
            call {:layer 1} Lemma_SetSize_Subset(parked->dom, LeftTickets(Mutators->dom));
            return;
        }
    }
}

yield procedure {:layer 1} Collector({:linear} tid: One Loc)
preserves call BarrierInv();
requires call CollectorInv(tid, false, false);
{
    call CreateMutators(tid);
    while (true)
        invariant {:yields} true;
        invariant call BarrierInv();
        invariant call CollectorInv(tid, false, false);
    {
        call SetBarrier(true);
        call BarrierInv() | CollectorInv(tid, true, false);
        call WaitForAllParked(tid);
        assert {:layer 1} (forall one_loc: One Loc:: Map_Contains(Mutators, one_loc) ==> Map_Contains(parked, One(Tag(one_loc->val, Left()))));
        call SetBarrier(false);
    }
}

yield procedure {:layer 1} CreateMutators({:linear} tid: One Loc)
preserves call BarrierInv();
preserves call CollectorInv(tid, false, false);
{
    var roles: [Role]bool;
    var {:linear} new_one_loc: One Loc;
    var {:linear} slots: UnitMap (One (Tag Role));
    var {:linear} left: One (Tag Role);
    var {:linear} right: One (Tag Role);

    if (*) {
        roles := Set_Empty();
        roles := Set_Add(roles, Left());
        roles := Set_Add(roles, Right());
        call new_one_loc, slots := Tags_New(roles);
        left := One(Tag(new_one_loc->val, Left()));
        right := One(Tag(new_one_loc->val, Right()));
        call One_Get(slots, left);
        call One_Get(slots, right);
        call {:layer 1} Assume(!Map_Contains(Mutators, new_one_loc));
        call AddMutator(new_one_loc);
        async call Mutator(left, right);
        call CreateMutators(tid);
    }
}
