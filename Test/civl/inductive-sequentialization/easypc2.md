we have locked requests

participant votes only needs reqid 

locked requests needs durations - set of requests 

committed_requests - non overlapping - main spec - Set of requests


var {:layer 0,1} locked_requests: [Pid](Set Request);
var {:layer 0,1} participant_votes: [Pid][ReqId]Vote; //or  partial map [Pid, reqid] -> YES() ==> lockedreqs has it // linear partial map
{:linear} Map ParticipantPiece Vote


var {:layer 0,1} committed_requests: (Set Request);



all coordinators share committed_requests

all the participants update locked_requests and votes

voting_action - updates participant_votes and locked_requests
decision_action - updates locked_requests

inv1 : committed_requests \subseteq  forall pid : locked_requests[pid] 

inv2: forall pid : locked_requests[pid] - reqid is distinct for any two. durations are non overlapping for any two distinct. 
How to show interference free?


inv1 and inv2 ==> inv3
inv3 : committed requests are not overlapping

inv4: forall pid: Set_contains(locked_requests[pid], req) <==>  participant_votes[pid, req] belongs to domain and value is YES. 


==> is needed when you send vote action, you have to show that inv2 is preserved. 
// all reqids are dis

make the whole coordinator atomic R*NL*
sync the call to decision action by making it left mover. (inline the atomic action proof rule bcoz left)
before the code block

pieces are sent to voting action. linear parameters. 
voting action yes or no in linear map of pvotes, when recive it will remove it no matter yes or no. 
pass to decision async action as parameter. 
decision action will if the decision was to abort, it will it going to remove from locked requests and pvotes remains same
if it was Commit, then we put it back pvotes. 


three pieces : 2 async actions, ytoy fragment. check interference for these. 

While voting_action must be async, decision_action would be a standard action. The reason is that decision_action will be "synchronized" in coordinator but voting action will not.

The implication is that your yield invariants will be checked for interference-freedom against only the yield-to-yield fragment in coordinator and voting_action (but not against decision_action whose effect will be included in the yield-to-yield fragment). I suspect this is important because I doubt the yield invariants are preserved by decision_action.

calling the async proc - but refined action not async - means you don't have to non-interference but you still need to commutativity and we can stick to our model of participants being not in the same place as coordinator.
decision action must be a left mover 
recieve action is right mover



# Pieces of the proof strategy

## Data Structures and Types

```
type Pid = int;
type Duration = int;
type ReqId;

datatype Vote { YES(), NO(), NULL() }
datatype Decision { COMMIT(), ABORT(), NONE() }
datatype Request { Request(id: ReqId, duration: Duration )}

type ParticipantPiece = Fraction ReqId Pid;

var locked_requests: [Pid](Set Request);
var committed_requests: (Set Request);
var {:linear} participant_votes: Map ParticipantPiece Vote
```


## Passing of linear params

Each piece from participant map is passed to voting
Voting puts it back in the map
Recieve removes each piece
We pass each piece to decision
If it was commit we put it back in pvotes


## Make the procedure look like R\*NL\* - so that the invariant can be simplified 

caller of coordinator for sending the pieces from somewhere
yield proc looks like(piece)
```
{
    create_asyncs voting for all pids (1 to n) // voting maybe right, but create_asyncs are left, we don't need ISR bcoz they preserve our invariant, and the inv has the information we need which + the block recieve give us what we want. 
    YieldBig() 
    call to proc recieve_vote for all pids (1 to n) // right
    update decision // non-mover
    async call to proc deciding (but refined action is not async) for all pids (1 to n) // left // try whatever is easy for putting back or not // inlining them
}
```

### Make voting right movers
check against other votings - update different parts of the global var so ok
check against recieve_vote - can be done using assume and assert 


### Since recieve is not async can we treat the recieve_vote action loop as N ? 
### For deciding loop - Same as recieve_vote loop?


## Invariants

```
[inv1] committed_requests \subseteq forall pid : locked_requests[pid]

[inv2] forall pid : locked_requests[pid] - reqid is distinct for any two && durations are non overlapping for any two distinct. 

[inv3] forall pid: Set_contains(locked_requests[pid], req) <==>  participant_votes[reqId, pid] belongs to domain and value is YES. 

[inv4] committed requests are not overlapping

```
### Proof using these invariants

```
inv3 && inv1 && inv2 ==> inv4
```

#### Checking non-interference for each of these invariants

Main atomic code blocks to check non-inteference against 
1. voting async action
2. ytoy fragment in coordinator

##### Voting action
```
checks if locked_requests does not becoming overlapping, then updates participant votes and locked requests

```
inv1 is preserved because it only makes locked requests bigger if anything

inv2 durations are not overlapping is checked by if condition and about reqid not being the same, you have a fraction of some reqid that means it is not present in the linear participant_votes map, and by inv2 we know that it is not present in locked requests, hence it can be added. 

inv3 they are updated together so it should hold after voting

inv4 committed requests is not touched


##### ytoy fragment
```
updates locked requests if decision is no
updates committed requests if decision is yes
```

inv1 : from inv3 and the fact that you have all votes before adding to committed requests you can say that inv1 is preserved

inv2 : things are only removed so it won't cause a problem

inv3 : they are removed together

inv4 : we get from inv2 and inv1


# To consider for later

Duration needs to be a range not integer

Voting can be made to answer no non-deterministically (but how does this help, because we already have voting as right mover without this no?)