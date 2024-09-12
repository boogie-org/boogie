
async action {:layer 1} action_main_s({:linear_in} send: One ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
refines {:IS_right} main_s' using Inv_s;
modifies pSet;
creates read_s;
{
    assume {:add_to_pool "A", 0, n} true;
    assert sps == AllMemIndexPieces(send->val);
    // assert channels[tid] == None();
    call create_asyncs((lambda pa:read_s :: pa->s == send->val && Set_Contains(sps, pa->perm->val)));
}
yield procedure {:layer 0} main_s({:linear_in} send: One ChannelPiece, {:linear_in} sps: Set MemIndexPiece);
refines action_main_s;

async action {:layer 2,3} main_s'({:linear_in} send: One ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
modifies pSet, contents;
{
    var snapshot: Snapshot;  
    var {:linear} one_s: One ChannelPiece;
    var {:linear} pieces: Set MemIndexPiece;

    assume {:add_to_pool "A", 0, n} true;
    assert sps == AllMemIndexPieces(send->val);
    // assert channels[tid] == None();
    assume (forall i:int :: 1 <= i && i <= n ==> (snapshot[i]->ts > mem[i]->ts || snapshot[i]== mem[i]));
    // call Set_Put(pSet, sps);
    // call Send(send, snapshot);
    call pieces := Set_Get(pSet, AllMemIndexPieces(send->val)->val);
    one_s := One(send->val);
    call Fractions_To_One(one_s, MemIndices(), pieces);
    call Send(one_s, snapshot);

}

async left action {:layer 1} read_s(s: ChannelPiece, {:linear_in} perm: One MemIndexPiece)
modifies snapshots, pSet, contents;
{
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;
    var {:linear} one_s: One ChannelPiece;
    var {:linear} pieces: Set MemIndexPiece;
    assert 1 <= perm->val->id && perm->val->id <= n;
    assume {:add_to_pool "A", 0, n} true;

    if (*) {
        assume {:add_to_pool "K", mem[perm->val->id]->ts, k} {:add_to_pool "V", mem[perm->val->id]->value, v} true;
        assume k > mem[perm->val->id]->ts; 
        snapshots[s->val][perm->val->id]:= StampedValue(k, v);
    } else {
        snapshots[s->val][perm->val->id]:= mem[perm->val->id];
    }
    call One_Put(pSet, perm);

    if (Set_IsSubset(AllMemIndexPieces(s), pSet)) {
        call pieces := Set_Get(pSet, AllMemIndexPieces(s)->val);
        one_s := One(s);
        call Fractions_To_One(one_s, MemIndices(), pieces);
        call Send(one_s, snapshots[s->val]);
    }
}

action {:layer 1} Inv_s({:linear_in} send: One ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
modifies snapshots, pSet, contents;
creates read_s;
{
    var {:pool "A"} j: int;
    var {:linear} sps': Set MemIndexPiece;
    var {:linear} done_set: Set MemIndexPiece;
    var {:linear} one_s: One ChannelPiece;
    var {:linear} pieces: Set MemIndexPiece;
    var choice: read_s;
    
    assert sps == AllMemIndexPieces(send->val);
    // assert channels[tid] == None();
    assume {:add_to_pool "A", 0, j+1, n} 0 <= j && j <= n;
    havoc snapshots;
    assume (forall i:int :: 1 <= i && i <= j ==> (snapshots[send->val->val][i]->ts > mem[i]->ts || snapshots[send->val->val][i]== mem[i]));

    // assume {:add_to_pool "D", Permission(tid, n)} true;
    sps' := sps;
    call done_set := Set_Get(sps', (lambda {:pool "D"} x: MemIndexPiece :: x->val == send->val && 1 <= x->id && x->id <= j && x->ids ==  MemIndices()));
    call Set_Put(pSet, done_set);

    if (j < n) {
        choice := read_s(send->val, One(Fraction(send->val, j+1, MemIndices())));
        // One(Permission(tid, j+1))
        // async action {:layer 1} {:exit_condition Set_IsSubset(AllMemIndexPieces(s), Set_Add(pSet, perm->val))} read_s(s: ChannelPiece, {:linear_in} perm: One MemIndexPiece)

// type Channel; // Send + Receive
// type ChannelPiece = Fraction (Loc Channel) ChannelOp; // Send or Receive piece
// type MemIndexPiece = Fraction ChannelPiece int; // Each mem index piece of Channel Piece
        assume {:add_to_pool "C", choice} true;
        // call create_asyncs((lambda pa:read_s :: pa->s == send->val && Set_Contains(sps, pa->perm->val)));
        // call create_asyncs((lambda {:pool "C" } pa:read_s :: j+1 <=  pa->perm->val->mem_index && pa->perm->val->mem_index <= n && pa->perm->val->tid == tid));
        call create_asyncs((lambda {:pool "C" } pa:read_s :: pa->s == send->val && j+1 <= pa->perm->val->id && pa->perm->val->id <= n && pa->perm->val->val == send->val && pa->perm->val->ids == MemIndices()));

        call set_choice(choice);
    } else {
        call pieces := Set_Get(pSet, AllMemIndexPieces(send->val)->val);
        one_s := One(send->val);
        call Fractions_To_One(one_s, MemIndices(), pieces);
        call Send(one_s, snapshots[send->val->val]);
    }
}

