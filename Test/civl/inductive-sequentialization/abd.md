## Algorithm 2 ABD simulation of a multi-writer register in a message-passing system.

Below is the original algorithm for reference:
```

function queryPhase():
    sn++
    broadcast ⟨"query",sn⟩ // sn is channel id
    wait for ≥ (n+1)/2  reply msgs to this query msg
    (v,u) := pair in reply msg with largest timestamp
    return (v,u)


when ⟨"query",s⟩ is received from q:
    send ⟨"reply",val,ts,s⟩ to q


function updatePhase(v,u):
    sn++
    broadcast ⟨"update",v, u, sn⟩
    wait for ≥ (n+1)/2 ack msgs for this update msg
    return

when ⟨"update",v,u,s⟩ is received from q:
    if u > ts then (val,ts) := (v,u)
    send ⟨"ack",s⟩ to q


Read(): // process calls this 
    (v,u) := queryPhase
    updatePhase(v,u) {write-back}
    return v


Write(v) for process with id i:
    (-, (t, -)) := queryPhase() {just need integer in timestamp}
    updatePhase(v,(t + 1))
    return

```
To prove: read and write to single register

## Types and Datastructures

```
type Value;
type ReqId;
type CId;
type PId = int;

datatype Timestamp{
    time: int, reqid: ReqId
}

datatype StampedValue {
    StampedValue(ts: Timestamp, value: Value)
} 

datatype ReqType { READ(), WRITE()}

datatype Request { Request(id: ReqId, type: ReqType, val: Option Value)}

type RequestPiece = Fraction ReqId Pid;
var participant_mem: [PId]StampedValue;
var participant_query_replies: Map RequestPiece StampedValue;
var participant_update_replies: Map RequestPiece StampedValue;
var coordinator_max_ts: [CId]int; // initially it is -1;
```

## Assumptions: 
1. no faults (everyone replies to the broadcast message).
2. Participants also use reqId to choose which timestamp update to pick.


## Model with read/write API

```
READ'(cid) returns result{
    local mem;
    return mem;
}
```

```
WRITE'(cid, v)'{
    local mem;
    mem = v;
}
```
> Are READ' and WRITE' making sense?

```
READ({:linear} cid, req: Request) returns result 
refines READ'
{
    local mem;

    < break reqId into pieces >

    create_asyncs Query(piece) // 1 to n // asyncs of right mover actions
    assume (all pieces in participant_query_replies)

    < get all pieces back to pass to update phase >
    
    mem = find max timestamped value among replies
    
    assume mem->ts >= coordinator_max_ts[cid]; // non-mover?
    coordinator_max_ts[cid] = mem->ts;

    create_asyncs Update(req, mem->ts, mem->value, piece) // 1 to n // L*
    assume (all pieces in participant_update_replies)

    return mem
}
```
> mem->ts >= coordinator_max_ts[cid]?
Inorder for the query to be a right mover, they need to be able to send old values. It is okay if some participants send old values, but if everyone does then it is a problem (because we don't meet the spec of the original algo). So the coordinator needs a way to identify and block in such cases. Hence this check. 

> why is cid required?
So that other coordinators don't interfere with coordinator_max_ts. We don't want this because the we would block some behaviors that are otherwise allowed by the original algorithm.

> Do we need both cid and reqId?

```
READ0 refines READ
{
    //before introducing coordinator_max_ts and assume
}
```
> Do we need to model READ0? If we do model, is it easy to get from READ0 to READ in civl?

```
WRITE({:linear} cid: CId, req: Request)
refines WRITE'
{
    local mem;

    //break reqId into pieces 

    create_asyncs Query(piece) // 1 to n // asyncs of right mover actions
    assume (all pieces in participant_query_replies)

    //get all pieces so that we can pass to update phase
    
    mem = find max timestamped value among replies
    
    assume mem->ts >= coordinator_max_ts[cid]; // non-mover?
    coordinator_max_ts[cid] = mem->ts;

    create_asyncs Update(mem->ts+1, req->val, piece) // 1 to n // L*
    assume (all pieces in participant_update_replies)
}
```

```
right Query(piece){
    if(*){
         var old_piece;
         assume old_piece->id == piece->id and participant_update_replies[old_piece] exists;
         participant_query_replies[piece] = participant_update_replies[old_piece];   
    }
    else{
          participant_query_replies[piece] = participant_mem[pid];
    }
}
```

```
left Update(ts, v, piece){
    if (ts, piece->val) > (participant_mem[piece->id]->ts) 
    {
        participant_mem[piece->id] = StampedValue(timestamp(ts, v), piece->val);
    }
    participant_update_replies[piece] = particpant_mem[piece->id];
}
```
> why is update a left mover? 
1. it always commutes w.r.t other updates because it also compares reqid. 
2. it commutes to query also, because query is a right mover. 

## Proof strategy

READ()/ WRITE() looks like R\*NL\*

## Other questions

### How do things change if we have (n+1)/2 replies only?
We can keep using coordinator_ts_max and I think it should work.

### How exactly do you plan to deal with a bunch or async right movers? What is your invariant that will summarize them?
participant_query_replies[piece] is either participant_update_replies[old_piece] or participant_mem[pid]

invariant (forall piece: Map_Contains(participant_query_replies, piece) ==>
                         Map_At(participant_query_replies, piece) is participant_update_replies[old_piece of same piece->id] or participant_mem[piece->id])
