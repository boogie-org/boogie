// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Value;

type Tid;

datatype StampedValue {
    StampedValue(ts: int, value: Value)
} 

type Channel; // Send + Receive
type ChannelPiece = Fraction (Loc Channel) ChannelOp; // Send or Receive piece
type MemIndexPiece = Fraction ChannelPiece int; // Each mem index piece of Channel Piece

type Snapshot = [int]StampedValue;

datatype ChannelOp {
    Receive(),
    SendFirst(),
    SendSecond()
}

function {:inline} ChannelOps(): Set ChannelOp {
  Set_Add(Set_Add(Set_Add(Set_Empty(), Receive()), SendFirst()), SendSecond())
}

function {:inline} IsReceive(piece: ChannelPiece): bool {
    piece == Fraction(piece->val, Receive(), ChannelOps())
}

function {:inline} IsSendFirst(piece: ChannelPiece): bool {
    piece == Fraction(piece->val, SendFirst(), ChannelOps())
}

function {:inline} IsSendSecond(piece: ChannelPiece): bool {
    piece == Fraction(piece->val, SendSecond(), ChannelOps())
}

function {:inline} ToSendFirst(piece: ChannelPiece): ChannelPiece {
    Fraction(piece->val, SendFirst(), piece->ids)
}

function {:inline} ToSendSecond(piece: ChannelPiece): ChannelPiece {
    Fraction(piece->val, SendSecond(), piece->ids)
}

const NumMemIndices: int;
axiom NumMemIndices >= 1;

var {:layer 0,3} mem: Snapshot;
var {:linear} {:layer 0,2} pSet: Set MemIndexPiece;
var {:layer 0,1} snapshots: [ChannelPiece]Snapshot; // domain contains only Send pieces
var {:linear} {:layer 0,2} contents: Map ChannelPiece Snapshot; // domain contains only Send pieces

function {:inline} AllMemIndexPieces(s: ChannelPiece): Set MemIndexPiece {
    Set((lambda {:pool "MemIndexPieces"} x: MemIndexPiece :: x->val == s && x->ids == MemIndices() && Set_Contains(x->ids, x->id)))
}

function {:inline} MemIndices(): Set int {
    Set((lambda {:pool "MemIndices"} x: int :: 1 <= x && x <= NumMemIndices))
}

function {:inline} IsValidMemIndexPiece(piece: MemIndexPiece): bool {
    Set_Contains(piece->ids, piece->id) &&
    piece->ids == MemIndices()
}

atomic action {:layer 1,2} SendFirst({:linear_in} one_s: One ChannelPiece, snapshot: Snapshot)
modifies contents;
{
    var {:linear} cell: Cell ChannelPiece Snapshot;

    assert IsSendFirst(one_s->val);
    call cell := Cell_Pack(one_s, snapshot);
    call Map_Put(contents, cell);
}

right action {:layer 1,2} action_ReceiveFirst({:linear} one_r: One ChannelPiece) returns ({:linear} one_s: One ChannelPiece, snapshot: Snapshot)
modifies contents;
{
    var {:linear} cell: Cell ChannelPiece Snapshot;
    var s: ChannelPiece;

    assert IsReceive(one_r->val);
    s := ToSendFirst(one_r->val);
    assume Map_Contains(contents, s);
    call cell := Map_Get(contents, s);
    call one_s, snapshot := Cell_Unpack(cell);
}
yield procedure {:layer 0} ReceiveFirst({:linear} one_r: One ChannelPiece) returns ({:linear} one_s: One ChannelPiece, snapshot: Snapshot);
refines action_ReceiveFirst;

atomic action {:layer 1,2} SendSecond({:linear_in} one_s: One ChannelPiece, snapshot: Snapshot)
modifies contents;
{
    var {:linear} cell: Cell ChannelPiece Snapshot;

    assert IsSendSecond(one_s->val);
    call cell := Cell_Pack(one_s, snapshot);
    call Map_Put(contents, cell);
}

right action {:layer 1,2} action_ReceiveSecond({:linear} one_r: One ChannelPiece) returns ({:linear} one_s: One ChannelPiece, snapshot: Snapshot)
modifies contents;
{
    var {:linear} cell: Cell ChannelPiece Snapshot;
    var s: ChannelPiece;

    assert IsReceive(one_r->val);
    s := ToSendSecond(one_r->val);
    assume Map_Contains(contents, s);
    call cell := Map_Get(contents, s);
    call one_s, snapshot := Cell_Unpack(cell);
}
yield procedure {:layer 0} ReceiveSecond({:linear} one_r: One ChannelPiece) returns ({:linear} one_s: One ChannelPiece, snapshot: Snapshot);
refines action_ReceiveSecond;

atomic action {:layer 3} GetSnapshot(
    loc_channel: Loc Channel, {:linear_in} one_r: One ChannelPiece, {:linear_in} one_s_first: One ChannelPiece, {:linear_in} one_s_second: One ChannelPiece)
    returns (snapshot: [int]StampedValue)
{
    assume (forall i:int :: 1 <= i && i <= NumMemIndices ==> snapshot[i] == mem[i]);
}
yield procedure {:layer 2} coordinator(
    loc_channel: Loc Channel, {:linear_in} one_r: One ChannelPiece, {:linear_in} one_s_first: One ChannelPiece, {:linear_in} one_s_second: One ChannelPiece)
    returns (snapshot: [int]StampedValue)
requires {:layer 2} one_r->val == Fraction(loc_channel, Receive(), ChannelOps());
requires {:layer 2} one_s_first->val == ToSendFirst(one_r->val);
requires {:layer 2} one_s_second->val == ToSendSecond(one_r->val);
refines GetSnapshot;
{
    var {:linear} sps: Set MemIndexPiece;
    var snapshot': Snapshot;
    var {:linear} one_s_first': One ChannelPiece;
    var {:linear} one_s_second': One ChannelPiece;

    one_s_first' := one_s_first;
    one_s_second' := one_s_second;

    while (true)
    invariant {:yields} true;
    invariant {:layer 2} one_s_first'->val == ToSendFirst(one_r->val);
    invariant {:layer 2} one_s_second'->val == ToSendSecond(one_r->val);
    {
        assert {:layer 2} !Map_Contains(contents, one_s_first'->val);
        call sps := One_To_Fractions(one_s_first', MemIndices());
        async call _main_f(one_s_first'->val, sps);

        par Yield() | YieldFirstScan(one_r, one_s_first'->val);

        call one_s_first', snapshot := ReceiveFirst(one_r);
        assert {:layer 2} (forall i:int :: 1 <= i && i <= NumMemIndices ==> (snapshot[i]->ts < mem[i]->ts || snapshot[i] == mem[i]));
        call sps := One_To_Fractions(one_s_second', MemIndices());
        call main_s(one_s_second'->val, sps);

        par Yield() | YieldSecondScan(one_r, one_s_second', snapshot, Map_At(contents, one_s_second'->val), mem);

        call one_s_second', snapshot' := ReceiveSecond(one_r);
        if (snapshot == snapshot') {
            assume false;
            return;
        }
    }
}

yield invariant {:layer 1} Yield();

yield invariant {:layer 2} YieldFirstScan({:linear} one_r: One ChannelPiece, s_first: ChannelPiece);
invariant IsReceive(one_r->val);
invariant s_first == ToSendFirst(one_r->val);
invariant Map_Contains(contents, s_first) ==>
            (var snapshot := Map_At(contents, s_first);
                (forall i:int :: 1 <= i && i <= NumMemIndices ==> (snapshot[i]->ts < mem[i]->ts || snapshot[i] == mem[i])));

yield invariant {:layer 2} YieldSecondScan({:linear} one_r: One ChannelPiece, one_s_second: One ChannelPiece, snapshot: Snapshot, snapshot': Snapshot, mem: Snapshot);
invariant IsReceive(one_r->val);
invariant one_s_second->val == ToSendSecond(one_r->val);
invariant Map_Contains(contents, one_s_second->val) && snapshot' == Map_At(contents, one_s_second->val);
invariant snapshot == snapshot' ==> (forall i:int :: 1 <= i && i <= NumMemIndices ==> snapshot[i] == mem[i]);

atomic action {:layer 1,2} write(i: int,v: Value)
modifies mem;
{
    var x: StampedValue;

    x := mem[i];
    mem[i] := StampedValue(x->ts + 1, v);
}
/////////////////////////////////////////////////////////////////////////////////////////////

async action {:layer 3} main_f''(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
{
    assert IsSendFirst(s);
    assert sps == AllMemIndexPieces(s);
}

async action {:layer 1} main_f(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
refines {:IS_right} main_f' using Inv_f;
modifies pSet;
creates read_f;
{
    assert IsSendFirst(s);
    assert sps == AllMemIndexPieces(s);
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume {:add_to_pool "Snapshot", snapshots[s]} true;
    call create_asyncs((lambda pa: read_f :: Set_Contains(sps, pa->perm->val)));
}
yield procedure {:layer 0} _main_f(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece);
refines main_f;

async action {:layer 2} main_f'(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
modifies pSet, contents;
refines main_f'';
requires {:layer 2} IsSendFirst(s) && sps == AllMemIndexPieces(s);
{
    var snapshot: Snapshot;  
    var {:linear} one_s: One ChannelPiece;

    assert IsSendFirst(s);
    assert sps == AllMemIndexPieces(s);
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume (forall i:int :: 1 <= i && i <= NumMemIndices ==> (snapshot[i]->ts < mem[i]->ts || snapshot[i] == mem[i]));
    one_s := One(s);
    call Fractions_To_One(one_s, MemIndices(), sps);
    call SendFirst(one_s, snapshot);
}

async action {:layer 1}
{:exit_condition Set_IsSubset(AllMemIndexPieces(perm->val->val), Set_Add(pSet, perm->val))}
read_f({:linear_in} perm: One MemIndexPiece)
modifies snapshots, pSet, contents;
{
    var {:pool "SV_read_f"} sv: StampedValue;
    var s: ChannelPiece;
    var {:linear} one_s: One ChannelPiece;
    var {:linear} pieces: Set MemIndexPiece;
    var piece: MemIndexPiece;

    piece := perm->val;
    assert IsSendFirst(piece->val) && IsValidMemIndexPiece(piece);
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume {:add_to_pool "SV_read_f", sv, mem[piece->id]} sv->ts < mem[piece->id]->ts || sv == mem[piece->id];
    s := piece->val;
    snapshots[s][piece->id] := sv;
    assume {:add_to_pool "Snapshot", snapshots[s]} true;
    call One_Put(pSet, perm);
    if (Set_IsSubset(AllMemIndexPieces(s), pSet)) {
        call pieces := Set_Get(pSet, AllMemIndexPieces(s)->val);
        one_s := One(s);
        call Fractions_To_One(one_s, MemIndices(), pieces);
        call SendFirst(one_s, snapshots[s]);
    }
}

action {:layer 1} Inv_f(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
modifies snapshots, pSet, contents;
creates read_f;
{
    var {:pool "MemIndices"} j: int;
    var {:linear} sps': Set MemIndexPiece;
    var {:linear} done_set: Set MemIndexPiece;
    var {:linear} one_s: One ChannelPiece;
    var {:linear} pieces: Set MemIndexPiece;
    var choice: read_f;
    var {:pool "Snapshot"} snapshot: Snapshot;
    
    assert IsSendFirst(s);
    assert sps == AllMemIndexPieces(s);
    assume {:add_to_pool "MemIndices", 0, j+1, NumMemIndices} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 1 <= i && i <= j ==> (snapshot[i]->ts < mem[i]->ts || snapshot[i]== mem[i]));
    snapshots[s] := snapshot;

    assume {:add_to_pool "MemIndexPieces",
            Fraction(s, NumMemIndices, MemIndices())
            , Fraction(s, j, MemIndices())
            , Fraction(s, j+1, MemIndices())
            } true;

    sps' := sps;
    call done_set := Set_Get(sps', (lambda {:pool "MemIndexPieces"} x: MemIndexPiece :: x->val == s && 1 <= x->id && x->id <= j && x->ids ==  MemIndices()));
    call Set_Put(pSet, done_set);

    if (j < NumMemIndices) {
        choice := read_f(One(Fraction(s, j+1, MemIndices())));
        assume {:add_to_pool "ReadPendingAsyncs", choice} true;
        call create_asyncs(
            (lambda {:pool "ReadPendingAsyncs"} pa: read_f ::
                j+1 <= pa->perm->val->id && pa->perm->val->id <= NumMemIndices && pa->perm->val->val == s && pa->perm->val->ids == MemIndices()));
        call set_choice(choice);
    } else {
        call pieces := Set_Get(pSet, AllMemIndexPieces(s)->val);
        one_s := One(s);
        call Fractions_To_One(one_s, MemIndices(), pieces);
        call SendFirst(one_s, snapshot);
    }
}

/////////////////////////////////////////////////////////////////////////////////////////////

async action {:layer 1} action_main_s(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
refines {:IS_left} main_s' using Inv_s;
modifies pSet;
creates read_s;
{
    assert IsSendSecond(s);
    assert sps == AllMemIndexPieces(s);
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume {:add_to_pool "Snapshot", snapshots[s]} true;
    call create_asyncs((lambda pa: read_s :: Set_Contains(sps, pa->perm->val)));
}
yield procedure {:layer 0} main_s(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece);
refines action_main_s;

async action {:layer 2} main_s'(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
modifies pSet, contents;
{
    var snapshot: Snapshot;  
    var {:linear} one_s: One ChannelPiece;

    assert IsSendSecond(s);
    assert sps == AllMemIndexPieces(s);
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume (forall i:int :: 1 <= i && i <= NumMemIndices ==> (snapshot[i]->ts > mem[i]->ts || snapshot[i] == mem[i]));
    one_s := One(s);
    call Fractions_To_One(one_s, MemIndices(), sps);
    call SendSecond(one_s, snapshot);
}

async left action {:layer 1} read_s({:linear_in} perm: One MemIndexPiece)
modifies snapshots, pSet, contents;
{
    var {:pool "SV_read_s"} sv: StampedValue;
    var s: ChannelPiece;
    var {:linear} one_s: One ChannelPiece;
    var {:linear} pieces: Set MemIndexPiece;
    var piece: MemIndexPiece;

    piece := perm->val;
    assert IsSendSecond(piece->val) && IsValidMemIndexPiece(piece);
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume {:add_to_pool "SV_read_s", sv, mem[piece->id]} sv->ts > mem[piece->id]->ts || sv == mem[piece->id];
    s := piece->val;
    snapshots[s][piece->id] := sv;
    assume {:add_to_pool "Snapshot", snapshots[s]} true;
    call One_Put(pSet, perm);
    if (Set_IsSubset(AllMemIndexPieces(s), pSet)) {
        call pieces := Set_Get(pSet, AllMemIndexPieces(s)->val);
        one_s := One(s);
        call Fractions_To_One(one_s, MemIndices(), pieces);
        call SendSecond(one_s, snapshots[s]);
    }
}

action {:layer 1} Inv_s(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
modifies snapshots, pSet, contents;
creates read_s;
{
    var {:pool "MemIndices"} j: int;
    var {:linear} sps': Set MemIndexPiece;
    var {:linear} done_set: Set MemIndexPiece;
    var {:linear} one_s: One ChannelPiece;
    var {:linear} pieces: Set MemIndexPiece;
    var choice: read_s;
    var {:pool "Snapshot"} snapshot: Snapshot;
    
    assert IsSendSecond(s);
    assert sps == AllMemIndexPieces(s);
    assume {:add_to_pool "MemIndices", 0, j+1, NumMemIndices} 0 <= j && j <= NumMemIndices;
    assume (forall i:int :: 1 <= i && i <= j ==> (snapshot[i]->ts > mem[i]->ts || snapshot[i]== mem[i]));
    snapshots[s] := snapshot;

    assume {:add_to_pool "MemIndexPieces",
            Fraction(s, NumMemIndices, MemIndices())
            , Fraction(s, j, MemIndices())
            , Fraction(s, j+1, MemIndices())
            } true;

    sps' := sps;
    call done_set := Set_Get(sps', (lambda {:pool "MemIndexPieces"} x: MemIndexPiece :: x->val == s && 1 <= x->id && x->id <= j && x->ids ==  MemIndices()));
    call Set_Put(pSet, done_set);

    if (j < NumMemIndices) {
        choice := read_s(One(Fraction(s, j+1, MemIndices())));
        assume {:add_to_pool "ReadPendingAsyncs", choice} true;
        call create_asyncs(
            (lambda {:pool "ReadPendingAsyncs"} pa: read_s ::
                j+1 <= pa->perm->val->id && pa->perm->val->id <= NumMemIndices && pa->perm->val->val == s && pa->perm->val->ids == MemIndices()));
        call set_choice(choice);
    } else {
        call pieces := Set_Get(pSet, AllMemIndexPieces(s)->val);
        one_s := One(s);
        call Fractions_To_One(one_s, MemIndices(), pieces);
        call SendSecond(one_s, snapshot);
    }
}