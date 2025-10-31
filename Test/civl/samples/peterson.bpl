// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
variables flag: [bool]bool, turn: bool;

process (self: bool) {
    while (true) {
        a1: flag[self] := true;
        a2: turn := !self;
        a3a: if (flag[!self]) {goto a3b} else {goto cs} ;
        a3b: if (turn != self) {goto a3a} else {goto cs} ;
        cs: /* critical section */ flag[self] := false;
    }
}
*/

datatype Label { a1(), a2(), a3a(), a3b(), cs() }

var {:layer 1,1} pc: [bool]Label;
var {:layer 0,1} turn: bool;
var {:layer 0,1} flag: [bool]bool;

function {:inline} PetersonPredicate(pc: [bool]Label, turn: bool, flag:[bool]bool, id: bool): bool {
    (pc[id] == cs() ==> pc[!id] != cs()) &&
    (pc[id] == cs() && (pc[!id] == a3a() || pc[!id] == a3b()) ==> turn == id) &&
    (pc[id] == a1() <==> !flag[id])
}

yield invariant {:layer 1} ProgramCounterInv({:linear} self: One bool, l: Label);
preserves pc[self->val] == l;

yield invariant {:layer 1} PetersonInv();
preserves PetersonPredicate(pc, turn, flag, false);
preserves PetersonPredicate(pc, turn, flag, true);

yield procedure {:layer 1} Peterson({:linear} self: One bool)
preserves call ProgramCounterInv(self, a1());
preserves call PetersonInv();
{
    var id: bool;
    var other_flag: bool;
    var _turn: bool;

    id := self->val;
    call SetFlag(id, true);
    call {:layer 1} pc := Copy(pc[id := a2()]); // pc[id] := a2()

    call ProgramCounterInv(self, a2()) | PetersonInv();

    call SetTurn(!id);
    call {:layer 1} pc := Copy(pc[id := a3a()]); // pc[id] := a3a()

    while (true)
    invariant {:layer 1} {:yields} true;
    invariant call ProgramCounterInv(self, a3a());
    invariant call PetersonInv();
    {
        call other_flag := GetFlag(!id);
        if (!other_flag) {
            break;
        }
        call {:layer 1} pc := Copy(pc[id := a3b()]); // pc[id] := a3b()

        call ProgramCounterInv(self, a3b()) | PetersonInv();

        call _turn := GetTurn();
        if (_turn == id) {
            break;
        }
        call {:layer 1} pc := Copy(pc[id := a3a()]); // pc[id] := a3a()
    }

    /* critical section */
    call {:layer 1} pc := Copy(pc[id := cs()]); // pc[id] := cs()
    call ProgramCounterInv(self, cs()) | PetersonInv();

    call SetFlag(id, false);
    call {:layer 1} pc := Copy(pc[id := a1()]); // pc[id] := a1()
}

yield procedure {:layer 0} SetFlag(id: bool, v: bool);
refines atomic action {:layer 1} _
{
    flag[id] := v; 
}

yield procedure {:layer 0} GetFlag(id: bool) returns (v: bool);
refines atomic action {:layer 1} _
{
    v := flag[id];
}

yield procedure {:layer 0} SetTurn(id: bool);
refines atomic action {:layer 1} _
{
    turn := id;
}

yield procedure {:layer 0} GetTurn() returns (id: bool);
refines atomic action {:layer 1} _
{
    id := turn;
}