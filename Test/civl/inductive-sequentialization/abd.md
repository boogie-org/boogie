Algorithm 2 ABD simulation of a multi-writer register in a message-passing system.
local variables:
sn, initially 0 {for readers and writers, sequence number used to identify messages} //process_id -> int
val, initially v0 {for servers, latest register value} //server_id -> set_of_values
ts, initially (0, 0) {for servers, timestamp of current register value, (integer, process id) pair} // server_id -> int(ts)
atmost half can crash (messages can't be lost)

channel= [pid1][pid2]int??

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

// To prove: read and write to single register


## Coordinator?

## Types and Datastructures


## Read' and Write' 

### Read' 

should look like it is reading directly from memory without querying everyone

### Write'

should look like it is writing directly to memory without updating everyone

## How to go from Read -> Read'?


## how to relate participant memory and memory?

## Coordinator



<!-- 
Coordinator'(req)
{
     if (req->type == READ()){
            all participant_mem looks exactly the same
            we return the one value
    }
    else if(req->type == WRITE()){
           all particiapnt_mem looks the same
           we 
    }
} --> -->



type Value;
type ReqId;
type Pid = int;

datatype StampedValue {
    StampedValue(ts: int, value: Value)
} 

datatype ReqType { READ(), WRITE()}

datatype Request { Request(id: ReqId, type: ReqType, val: Option Value)}

type RequestPiece = Fraction ReqId Pid;
var participant_mem: [Pid]StampedValue;
var participant_read_replies: Map RequestPiece StampedValue;
var participant_update_replies: Map RequestPiece bool;


client talks to coordinator
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
Coordinator(req) returns mem {
    local mem;
    create_asyncs to Participant_action(Read req, piece) /1 to n
    if (req->type == READ()){
            block until (n+1)/2 pieces in participant_read_replies
            mem = find max timestamped value
            create_asyncs to Participant_action(Write req)
            block until (n+1)/2 pieces in participant_write_replies
            and return mem
    }
    else if(req->type == WRITE()){
            block until (n+1)/2 pieces in participant_read_replies
            mem = find max timestamped value
            create_asyncs to Participant_action(Write req, mem+1)
            block until (n+1)/2 pieces in participant_write_replies
            return
    }
}

Participant_action(req, piece) {
    if(req->type == READ()){
        participant_read_replies[piece] = participant_mem[pid];
    }
    else if(req->type == WRITE())
    {
        if participant_mem[pid]->ts < req->val->ts:
            participant_mem[pid][] = req->val;
            participant_write_replies[piece] = true;
    }
}

//proof strategy

No fixed linearization points (no single point where read or write happens, may depend on what happens in the future) (no single syntactic point in the program) (ex: snapshot, so the non-det abstraction helps and this issue does not show up)
how does lin point in syntactic help? skip* sth skip* refinement proofs (ex: trieber stack)

intersection of majority, two consecutive reads the second read does not return an older value (inv)

two parallel writes, same time query phase - may get diff values


