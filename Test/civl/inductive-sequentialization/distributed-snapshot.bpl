// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Value;

type Tid;

datatype StampedValue {
    StampedValue(ts: int, value: Value)
} 

type Channel; // Send + Receive
type ChannelPiece = Fraction (Loc Channel) ChannelOp; // SendFirst or SendSecond or Receive piece
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

function {:inline} ToReceive(loc_channel: Loc Channel): ChannelPiece {
    Fraction(loc_channel, Receive(), ChannelOps())
}

function {:inline} ToSendFirst(loc_channel: Loc Channel): ChannelPiece {
    Fraction(loc_channel, SendFirst(), ChannelOps())
}

function {:inline} ToSendSecond(loc_channel: Loc Channel): ChannelPiece {
    Fraction(loc_channel, SendSecond(), ChannelOps())
}

const NumMemIndices: int;
axiom NumMemIndices >= 1;

function {:inline} MemIndexPieces(s: ChannelPiece, j: int): Set MemIndexPiece {
    Set((lambda {:pool "MemIndexPieces"} x: MemIndexPiece :: x->val == s && x->ids == MemIndices() && 1 <= x->id && x->id <= j))
}

function {:inline} AllMemIndexPieces(s: ChannelPiece): Set MemIndexPiece {
    MemIndexPieces(s, NumMemIndices)
}

function {:inline} MemIndices(): Set int {
    Set((lambda {:pool "MemIndices"} x: int :: 1 <= x && x <= NumMemIndices))
}

function {:inline} IsValidMemIndexPiece(piece: MemIndexPiece): bool {
    Set_Contains(piece->ids, piece->id) &&
    piece->ids == MemIndices()
}

function {:inline} MemIndexPiece(cp: ChannelPiece, i: int): MemIndexPiece
{
    Fraction(cp, i, MemIndices())
}

var {:layer 0,3} mem: Snapshot;
var {:linear} {:layer 0,2} pset: Map MemIndexPiece StampedValue;

atomic action {:layer 3} GetSnapshot({:linear_in} one_loc_channel: One (Loc Channel)) returns (snapshot: [int]StampedValue)
{
    assume (forall i:int :: 1 <= i && i <= NumMemIndices ==> snapshot[i] == mem[i]);
}
yield procedure {:layer 2} Coordinator({:linear_in} one_loc_channel: One (Loc Channel)) returns (snapshot: [int]StampedValue)
refines GetSnapshot;
{
    var {:linear} channelOps: Set ChannelPiece;
    var {:linear} one_r: One ChannelPiece;
    var {:linear} one_s_first: One ChannelPiece;
    var {:linear} one_s_second: One ChannelPiece;
    var {:linear} sps_first: Set MemIndexPiece;
    var {:linear} sps_second: Set MemIndexPiece;
    var snapshot': Snapshot;

    call channelOps := One_To_Fractions(one_loc_channel, ChannelOps());
    call one_r := One_Get(channelOps, ToReceive(one_loc_channel->val));
    call one_s_first := One_Get(channelOps, ToSendFirst(one_loc_channel->val));
    call one_s_second := One_Get(channelOps, ToSendSecond(one_loc_channel->val));
    call sps_first := One_To_Fractions(one_s_first, MemIndices());
    call sps_second := One_To_Fractions(one_s_second, MemIndices());

    while (true)
    invariant {:yields} true;
    invariant {:layer 2} sps_first == AllMemIndexPieces(one_s_first->val);
    invariant {:layer 2} sps_second == AllMemIndexPieces(one_s_second->val);
    {
        async call {:skip} _main_f(one_s_first->val, sps_first);
        par Yield() | YieldFirstScan(one_r, one_s_first->val); // like proving an assertion that is non-interference free (Owicki-gries)
        call sps_first, snapshot := _ReceiveFirst(one_r, one_s_first->val); // right
        call _main_s(one_s_second->val, sps_second); // non // why not have yield inv similar to first phase // L*
        call sps_second, snapshot' := _ReceiveSecond(one_r, one_s_second->val); // left
        if (snapshot == snapshot') {
            return;
        }
    }
}

yield invariant {:layer 1} Yield();

yield invariant {:layer 2} YieldFirstScan({:linear} one_r: One ChannelPiece, s_first: ChannelPiece);
invariant IsReceive(one_r->val);
invariant s_first == ToSendFirst(one_r->val->val);
invariant (forall piece: MemIndexPiece :: Set_Contains(AllMemIndexPieces(s_first), piece) && Map_Contains(pset, piece) ==>
                                          Map_At(pset, piece)->ts < mem[piece->id]->ts || Map_At(pset, piece) == mem[piece->id]); // we don't need to actually read less in read_f for this to hold. 
//summary is not preserved? Is there any example where the async actions of ISR don't preserve the summary?
//whether ISR gives more power? or simplifies anything? maybe if order matters for something then they can be useful. 
//

left action {:layer 2} ReceiveSecond({:linear} one_r: One ChannelPiece, s: ChannelPiece) returns ({:linear} sps: Set MemIndexPiece, snapshot: Snapshot)
modifies pset;
asserts one_r->val->val == s->val;
asserts IsReceive(one_r->val);
asserts IsSendSecond(s);
asserts Set_IsSubset(AllMemIndexPieces(s), pset->dom);
{
    var {:linear} map: Map MemIndexPiece StampedValue;
    var data: [MemIndexPiece]StampedValue;

    call map := Map_Split(pset, AllMemIndexPieces(s));
    call sps, data := Map_Unpack(map);
    snapshot := (lambda x: int :: data[Fraction(s, x, MemIndices())]);
}
yield procedure {:layer 1} _ReceiveSecond({:linear} one_r: One ChannelPiece, s: ChannelPiece) returns ({:linear} sps: Set MemIndexPiece, snapshot: Snapshot)
refines ReceiveSecond;
{
    call sps, snapshot := _ReceiveFirst(one_r, s);
}

right action {:layer 1,2} ReceiveFirst({:linear} one_r: One ChannelPiece, s: ChannelPiece) returns ({:linear} sps: Set MemIndexPiece, snapshot: Snapshot)
modifies pset;
asserts one_r->val->val == s->val;
asserts IsReceive(one_r->val);
asserts IsSendFirst(s) || IsSendSecond(s);
{
    var {:linear} map: Map MemIndexPiece StampedValue;
    var data: [MemIndexPiece]StampedValue;

    assume Set_IsSubset(AllMemIndexPieces(s), pset->dom);
    call map := Map_Split(pset, AllMemIndexPieces(s));
    call sps, data := Map_Unpack(map);
    snapshot := (lambda x: int :: data[Fraction(s, x, MemIndices())]);
}
yield procedure {:layer 0} _ReceiveFirst({:linear} one_r: One ChannelPiece, s: ChannelPiece) returns ({:linear} sps: Set MemIndexPiece, snapshot: Snapshot);
refines ReceiveFirst;

async atomic action {:layer 1,2} write(i: int,v: Value)
modifies mem;
{
    var x: StampedValue;

    x := mem[i];
    mem[i] := StampedValue(x->ts + 1, v);
}
/////////////////////////////////////////////////////////////////////////////////////////////

async action {:layer 2} main_f'(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
modifies pset;
asserts IsSendFirst(s);
asserts sps == AllMemIndexPieces(s);
{
    var {:pool "Data"} data: [MemIndexPiece]StampedValue;
    var {:linear} map: Map MemIndexPiece StampedValue;

    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    assume (forall i: int :: 1 <= i && i <= NumMemIndices ==> (var x := MemIndexPiece(s, i); data[x]->ts < mem[i]->ts || data[x] == mem[i]));
    call map := Map_Pack(sps, data);
    call Map_Join(pset, map);
}

async action {:layer 1} main_f(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
refines {:IS_right} main_f' using Inv_f;
creates read_f;
asserts IsSendFirst(s);
asserts sps == AllMemIndexPieces(s);
{
    var data: [MemIndexPiece]StampedValue;

    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    call {:linear sps} create_asyncs((lambda pa: read_f :: Set_Contains(sps, pa->perm->val))); // What is {:linear sps???}
}
yield procedure {:layer 0} _main_f(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece);
refines main_f;

async action {:layer 1}
{:exit_condition Set_IsSubset(AllMemIndexPieces(perm->val->val), Set_Add(pset->dom, perm->val))}
read_f({:linear_in} perm: One MemIndexPiece)
modifies pset;
// asserts !exit_condition
asserts IsSendFirst(perm->val->val) && IsValidMemIndexPiece(perm->val);
// requires !exit
// ensures exit
{
    var {:pool "SV_read_f"} sv: StampedValue;
    var piece: MemIndexPiece;
    var {:linear} cell: Cell MemIndexPiece StampedValue;

    piece := perm->val;
    assume {:add_to_pool "MemIndexPieces", piece} true;
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume {:add_to_pool "SV_read_f", sv, mem[piece->id]} sv->ts < mem[piece->id]->ts || sv == mem[piece->id];
    call cell := Cell_Pack(perm, sv);
    call Map_Put(pset, cell);
    assume {:add_to_pool "Data", pset->val} true;
}

action {:layer 1} Inv_f(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
modifies pset;
creates read_f;
asserts IsSendFirst(s);
asserts sps == AllMemIndexPieces(s);
{
    var {:pool "MemIndices"} j: int;
    var {:linear} sps': Set MemIndexPiece;
    var {:linear} done_set: Set MemIndexPiece;
    var choice: read_f;
    var {:linear} map: Map MemIndexPiece StampedValue;
    var {:pool "Data"} data: [MemIndexPiece]StampedValue;
    
    assume {:add_to_pool "MemIndices", 0, j+1, NumMemIndices} {:add_to_pool "Data", data} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 1 <= i && i <= j ==> (var x := MemIndexPiece(s, i); data[x]->ts < mem[i]->ts || data[x] == mem[i]));

    sps' := sps;
    call done_set := Set_Get(sps', MemIndexPieces(s, j)->val);
    call map := Map_Pack(done_set, data);
    call Map_Join(pset, map);

    if (j < NumMemIndices) {
        choice := read_f(One(Fraction(s, j+1, MemIndices())));
        call set_choice(choice);
        assume {:add_to_pool "Read_PAs", choice} true;
        call {:linear sps'} create_asyncs((lambda {:pool "Read_PAs"} pa: read_f :: Set_Contains(sps', pa->perm->val)));
    }
}

/////////////////////////////////////////////////////////////////////////////////////////////

async action {:layer 2} main_s'(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
modifies pset;
asserts IsSendSecond(s);
asserts sps == AllMemIndexPieces(s);
{
    var {:pool "Data"} data: [MemIndexPiece]StampedValue;
    var {:linear} map: Map MemIndexPiece StampedValue;

    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    assume (forall i: int :: 1 <= i && i <= NumMemIndices ==> (var x := MemIndexPiece(s, i); data[x]->ts > mem[i]->ts || data[x] == mem[i]));
    call map := Map_Pack(sps, data);
    call Map_Join(pset, map);
}

async action {:layer 1} main_s(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
refines {:IS_left} main_s' using Inv_s;
creates read_s;
asserts IsSendSecond(s);
asserts sps == AllMemIndexPieces(s);
{
    var data: [MemIndexPiece]StampedValue;

    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    call {:linear sps} create_asyncs((lambda pa: read_s :: Set_Contains(sps, pa->perm->val)));
}
yield procedure {:layer 0} _main_s(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece);
refines main_s;

async left action {:layer 1} read_s({:linear_in} perm: One MemIndexPiece)
modifies pset;
asserts {:add_to_pool "SV_read_s", mem[perm->val->id]} IsSendSecond(perm->val->val) && IsValidMemIndexPiece(perm->val);
{
    var {:pool "SV_read_s"} sv: StampedValue;
    var piece: MemIndexPiece;
    var {:linear} cell: Cell MemIndexPiece StampedValue;

    piece := perm->val;
    assume {:add_to_pool "MemIndexPieces", piece} true;
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume {:add_to_pool "SV_read_s", sv, mem[piece->id]} sv->ts > mem[piece->id]->ts || sv == mem[piece->id];
    call cell := Cell_Pack(perm, sv);
    call Map_Put(pset, cell);
    assume {:add_to_pool "Data", pset->val} true;
}

action {:layer 1} Inv_s(s: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
modifies pset;
creates read_s;
asserts IsSendSecond(s);
asserts sps == AllMemIndexPieces(s);
{
    var {:pool "MemIndices"} j: int;
    var {:linear} sps': Set MemIndexPiece;
    var {:linear} done_set: Set MemIndexPiece;
    var choice: read_s;
    var {:linear} map: Map MemIndexPiece StampedValue;
    var {:pool "Data"} data: [MemIndexPiece]StampedValue;
    
    assume {:add_to_pool "MemIndices", 0, j+1, NumMemIndices} {:add_to_pool "Data", data} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 1 <= i && i <= j ==> (var x := MemIndexPiece(s, i); data[x]->ts > mem[i]->ts || data[x] == mem[i]));

    sps' := sps;
    call done_set := Set_Get(sps', MemIndexPieces(s, j)->val);
    call map := Map_Pack(done_set, data);
    call Map_Join(pset, map);

    if (j < NumMemIndices) {
        choice := read_s(One(Fraction(s, j+1, MemIndices())));
        call set_choice(choice);
        assume {:add_to_pool "Read_PAs", choice} true;
        call {:linear sps'} create_asyncs((lambda {:pool "Read_PAs"} pa: read_s :: Set_Contains(sps', pa->perm->val)));
    }
}