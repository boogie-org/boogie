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
type Pid = int;

datatype StampedValue {
    StampedValue(ts: int, value: Value)
} 

datatype ReqType { READ(), WRITE()}

datatype Request { Request(id: ReqId, type: ReqType, val: Option Value)}

type RequestPiece = Fraction ReqId Pid;
var participant_mem: [Pid](StampedValue, ReqId);
var participant_read_replies: Map RequestPiece StampedValue;
var participant_update_replies: Map RequestPiece bool;
var coordinator_max_ts: int; // initially it is -1;
```

## Model: Coordinator

client talks to coordinator

Assumptions: 
1. no faults (everyone replies to the broadcast message)

```
Coordinator'(req) returns value
{
    local mem;
     if (req->type == READ()){
          reads from mem
    }
    else if(req->type == WRITE()){
          write to mem
    }
}
```

```
Coordinator(req) returns mem 
refines Coordinator'
{
    local mem;
    create_asyncs Query() // 1 to n // R*
    assume (all pieces in participant_read_replies)
    
    mem = find max timestamped value among replies
    
    assume mem->ts >= coordinator_max_ts; // N
    coordinator_max_ts = mem->ts;

    if (req->type == READ()){
            create_asyncs Update(req, mem->ts, mem->value, piece) // 1 to n // L*
            assume (all pieces in participant_write_replies)
            and return mem
    }
    else if(req->type == WRITE()){  
            create_asyncs Update(req, mem->ts+1, req->val, piece) // 1 to n // L*
            assume (all pieces in participant_write_replies)
            return
    }
}
```

```
right Query(req, piece){
    if(*){
         var old_piece;
         assume old_piece->id == pid and participant_read_replies[old_piece] exists;
         participant_read_replies[piece] = participant_read_replies[old_piece];   
    }
    else{
          participant_read_replies[piece] = participant_mem[pid];
    }
}
```

```
left Update(req, ts, v, piece){
    if (req->val->ts, reqid) > (participant_mem[pid]->ts, participant_mem[pid]->reqid) 
    {
        participant_mem[pid] = (v, req->id);
    }
    participant_write_replies[piece] = true;
}
```

## Proof strategy

Coordinator looks like R\*NL\*

