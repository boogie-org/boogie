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

