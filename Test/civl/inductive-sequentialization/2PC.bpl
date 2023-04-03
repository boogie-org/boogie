// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "pid"} Pid = int;

// A type for vote messages of participants
datatype vote { YES(), NO() }

// A type for decision message of the coordinator
datatype decision { COMMIT(), ABORT(), NONE() }

// Number of participants
const n:int;
axiom n > 0;

// Participants have IDs from 1 to n, and the coordinator has ID 0.
function {:inline} pid (pid:int) : bool { 1 <= pid && pid <= n }
function {:inline} pidLe (pid:int, k:int) : bool { 1 <= pid && pid <= k }
function {:inline} pidGt (pid:int, k:int) : bool { k < pid && pid <= n }

// Channel of the participants for request messages from the coordinator
var {:layer 0,6} RequestChannel:[int]int;
// Channel of the participants for decision messages from the coordinator
var {:layer 0,6} DecisionChannel:[int][decision]int;
// Channel of the coordinator for vote messages from the participants
var {:layer 0,6} VoteChannel:[vote]int;
// Participant votes
var {:layer 0,6} votes:[int]vote;
// Coordinator and participant decisions
var {:layer 0,6} decisions:[int]decision;

////////////////////////////////////////////////////////////////////////////////

function {:inline} Init(pids:[int]bool, RequestChannel:[int]int, VoteChannel:[vote]int,
  DecisionChannel:[int][decision]int, decisions:[int]decision) : bool
{
  pids == MapConst(true) &&
  RequestChannel == (lambda i:int :: 0) &&
  VoteChannel == (lambda v:vote :: 0) &&
  DecisionChannel == (lambda i:int :: (lambda d:decision :: 0)) &&
  decisions == (lambda i:int :: NONE())
}

////////////////////////////////////////////////////////////////////////////////

action {:layer 6}
MAIN5 ({:linear_in "pid"} pids:[int]bool)
modifies RequestChannel, VoteChannel, votes, decisions;
{
  var dec:decision;
  assert Init(pids, RequestChannel, VoteChannel, DecisionChannel, decisions);
  havoc RequestChannel, VoteChannel, votes, decisions;
  if (*) { dec := COMMIT(); } else { dec := ABORT(); }
  assume dec == COMMIT() ==> (forall i:int :: pid(i) ==> votes[i] == YES());
  assume (forall i:int :: (i == 0 || pid(i)) ==> decisions[i] == dec);
}

invariant action {:layer 5} INV4 ({:linear_in "pid"} pids:[int]bool)
creates PARTICIPANT2;
modifies RequestChannel, VoteChannel, DecisionChannel, votes, decisions;
{
  var {:pool "INV1"} k: int;

  assert Init(pids, RequestChannel, VoteChannel, DecisionChannel, decisions);

  assume
    {:add_to_pool "INV1", k, k+1}
    {:add_to_pool "PARTICIPANT2", PARTICIPANT2(n)}
    0 <= k && k <= n;
  havoc RequestChannel, VoteChannel, votes, decisions;
  assume
    (decisions[0] == COMMIT() || decisions[0] == ABORT()) &&
    (decisions[0] == COMMIT() ==> (forall i:int :: pid(i) ==> votes[i] == YES())) &&
    (forall i:int :: pidLe(i,k) ==> decisions[i] == decisions[0]);
  DecisionChannel := (lambda i:int :: (lambda d:decision :: if pidGt(i, k) && d == decisions[0] then 1 else 0));
  call create_asyncs((lambda {:pool "PARTICIPANT2"} pa:PARTICIPANT2 :: pidGt(pa->pid, k)));
  call set_choice(PARTICIPANT2(k+1));
}

abstract action {:layer 5} PARTICIPANT2' ({:linear_in "pid"} pid:int)
modifies DecisionChannel, decisions;
{
  assert DecisionChannel[pid][COMMIT()] > 0 || DecisionChannel[pid][ABORT()] > 0;
  call PARTICIPANT2(pid);
}

////////////////////////////////////////////////////////////////////////////////

action {:layer 5} MAIN4 ({:linear_in "pid"} pids:[int]bool)
refines MAIN5 using INV4;
creates PARTICIPANT2;
eliminates PARTICIPANT2 using PARTICIPANT2';
modifies RequestChannel, VoteChannel, DecisionChannel, votes, decisions;
{
  var dec:decision;
  assert Init(pids, RequestChannel, VoteChannel, DecisionChannel, decisions);

  assume {:add_to_pool "INV1", 0} true;
  havoc RequestChannel, VoteChannel, votes;
  if (*) { dec := COMMIT(); } else { dec := ABORT(); }
  assume dec == COMMIT() ==> (forall i:int :: pid(i) ==> votes[i] == YES());
  decisions[0] := dec;
  DecisionChannel := (lambda i:int :: (lambda d:decision :: if pid(i) && d == dec then 1 else 0));
  call create_asyncs((lambda pa:PARTICIPANT2 :: pid(pa->pid)));
}

invariant action {:layer 4}
INV3 ({:linear_in "pid"} pids:[int]bool)
creates COORDINATOR2, PARTICIPANT2;
modifies RequestChannel, VoteChannel, DecisionChannel, votes, decisions;
{
  var dec:decision;
  assert Init(pids, RequestChannel, VoteChannel, DecisionChannel, decisions);

  havoc RequestChannel, VoteChannel, votes;

  if (*)
  {
    assume VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0;
    assume VoteChannel[YES()] + VoteChannel[NO()] <= n;
    assume VoteChannel[YES()] == n ==> (forall i:int :: pid(i) ==> votes[i] == YES());
    call create_async(COORDINATOR2(0));
    call create_asyncs((lambda pa:PARTICIPANT2 :: pid(pa->pid)));
  }
  else
  {
    if (*) { dec := COMMIT(); } else { dec := ABORT(); }
    assume dec == COMMIT() ==> (forall i:int :: pid(i) ==> votes[i] == YES());
    decisions[0] := dec;
    DecisionChannel := (lambda i:int :: (lambda d:decision :: if pid(i) && d == dec then 1 else 0));
    call create_asyncs((lambda pa:PARTICIPANT2 :: pid(pa->pid)));
  }
}

////////////////////////////////////////////////////////////////////////////////

action {:layer 4} MAIN3 ({:linear_in "pid"} pids:[int]bool)
refines MAIN4 using INV3;
creates COORDINATOR2, PARTICIPANT2;
modifies RequestChannel, VoteChannel, votes;
{
  assert Init(pids, RequestChannel, VoteChannel, DecisionChannel, decisions);
  havoc RequestChannel, VoteChannel, votes;
  assume VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0;
  assume VoteChannel[YES()] + VoteChannel[NO()] <= n;
  assume VoteChannel[YES()] == n ==> (forall i:int :: pid(i) ==> votes[i] == YES());
  call create_async(COORDINATOR2(0));
  call create_asyncs((lambda pa:PARTICIPANT2 :: pid(pa->pid)));
}

invariant action {:layer 3}
INV2 ({:linear_in "pid"} pids:[int]bool)
creates COORDINATOR2, PARTICIPANT1, PARTICIPANT2;
modifies RequestChannel, VoteChannel, votes;
{
  var {:pool "INV2"} k: int;

  assert Init(pids, RequestChannel, VoteChannel, DecisionChannel, decisions);

  havoc RequestChannel, VoteChannel, votes;
  assume
    {:add_to_pool "INV2", k, k+1}
    {:add_to_pool "PARTICIPANT1", PARTICIPANT1(n)}
    0 <= k && k <= n;
  assume (forall i:int :: pidGt(i,k) ==> RequestChannel[i] == 1) &&
    VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0 &&
    VoteChannel[YES()] + VoteChannel[NO()] <= k &&
    (VoteChannel[YES()] == k ==> (forall i:int :: pidLe(i,k) ==> votes[i] == YES()));
  call create_async(COORDINATOR2(0));
  call create_asyncs((lambda pa:PARTICIPANT2 :: pidLe(pa->pid, k)));
  call create_asyncs((lambda {:pool "PARTICIPANT1"} pa:PARTICIPANT1 :: pidGt(pa->pid, k)));
  call set_choice(PARTICIPANT1(k+1));
}

////////////////////////////////////////////////////////////////////////////////

action {:layer 3} MAIN2 ({:linear_in "pid"} pids:[int]bool)
refines MAIN3 using INV2;
creates COORDINATOR2, PARTICIPANT1;
modifies RequestChannel;
{
  assert Init(pids, RequestChannel, VoteChannel, DecisionChannel, decisions);

  assume {:add_to_pool "INV2", 0} true;
  RequestChannel := (lambda i:int :: if pid(i) then 1 else 0);
  call create_async(COORDINATOR2(0));
  call create_asyncs((lambda pa:PARTICIPANT1 :: pid(pa->pid)));
}

invariant action {:layer 2}
INV1 ({:linear_in "pid"} pids:[int]bool)
creates COORDINATOR1, COORDINATOR2, PARTICIPANT1;
modifies RequestChannel;
{
  assert Init(pids, RequestChannel, VoteChannel, DecisionChannel, decisions);
  if (*)
  {
    call create_async(COORDINATOR1(0));
    call create_asyncs((lambda pa:PARTICIPANT1 :: pid(pa->pid)));
  }
  else
  {
    RequestChannel := (lambda i:int :: if pid(i) then 1 else 0);
    call create_async(COORDINATOR2(0));
    call create_asyncs((lambda pa:PARTICIPANT1 :: pid(pa->pid)));
  }
}

////////////////////////////////////////////////////////////////////////////////

action {:layer 2} MAIN1 ({:linear_in "pid"} pids:[int]bool)
refines MAIN2 using INV1;
creates COORDINATOR1, PARTICIPANT1;
{
  assert Init(pids, RequestChannel, VoteChannel, DecisionChannel, decisions);
  call create_async(COORDINATOR1(0));
  call create_asyncs((lambda pa:PARTICIPANT1 :: pid(pa->pid)));
}

async action {:layer 2,3} PARTICIPANT1 ({:linear_in "pid"} pid:int)
creates PARTICIPANT2;
modifies RequestChannel, VoteChannel, votes;
{
  var v:vote;
  assert pid(pid);

  if (*)
  {
    assume RequestChannel[pid] > 0;
    RequestChannel[pid] := RequestChannel[pid] - 1;
    if (*) { v := YES(); } else { v := NO(); }
    votes[pid] := v;
    VoteChannel[v] := VoteChannel[v] + 1;
  }

  call create_async(PARTICIPANT2(pid));
}

async action {:layer 2,5} PARTICIPANT2 ({:linear_in "pid"} pid:int)
modifies DecisionChannel, decisions;
{
  var d:decision;
  assert pid(pid);
  assert DecisionChannel[pid][NONE()] == 0;
  if (*) { d := COMMIT(); } else { d := ABORT(); }
  assume DecisionChannel[pid][d] > 0;
  DecisionChannel[pid][d] := DecisionChannel[pid][d] - 1;
  decisions[pid] := d;
}

async <- action {:layer 2} COORDINATOR1 ({:linear_in "pid"} pid:int)
creates COORDINATOR2;
modifies RequestChannel;
{
  assert pid == 0;
  RequestChannel := (lambda i:int :: if pid(i) then RequestChannel[i] + 1 else RequestChannel[i]);
  call create_async(COORDINATOR2(0));
}

async action {:layer 2,4} COORDINATOR2 ({:linear_in "pid"} pid:int)
modifies VoteChannel, DecisionChannel, decisions;
{
  var dec:decision;
  assert pid == 0;

  if (*)
  {
    assume VoteChannel[YES()] >= n;
    dec := COMMIT();
  }
  else
  {
    dec := ABORT();
  }

  decisions[pid] := dec;
  havoc VoteChannel;
  DecisionChannel := (lambda i:int :: (lambda d:decision :: if pid(i) && d == dec then DecisionChannel[i][d] + 1 else DecisionChannel[i][d]));
}

////////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 1} YieldInit({:linear "pid"} pids:[int]bool);
invariant Init(pids, RequestChannel, VoteChannel, DecisionChannel, decisions);

yield procedure {:layer 1} main ({:linear_in "pid"} pids:[int]bool)
refines MAIN1;
requires call YieldInit(pids);
{
  var i:int;
  var {:pending_async}{:layer 1} Coordinator1_PAs:[COORDINATOR1]int;
  var {:pending_async}{:layer 1} Participant1_PAs:[PARTICIPANT1]int;
  var {:linear "pid"} pid:int;
  var {:linear "pid"} pids':[int]bool;

  pids' := pids;
  call pid, pids' := linear_transfer(0, pids');
  async call coordinator1(pid);
  i := 1;
  while (i <= n)
  invariant {:layer 1} 1 <= i && i <= n+1;
  invariant {:layer 1} (forall ii:int :: pid(ii) && ii >= i ==> pids'[ii]);
  invariant {:layer 1} Coordinator1_PAs == MapConst(0)[COORDINATOR1(0) := 1];
  invariant {:layer 1} Participant1_PAs == (lambda pa:PARTICIPANT1 :: if pid(pa->pid) && pa->pid < i then 1 else 0);
  {
    call pid, pids' := linear_transfer(i, pids');
    async call participant1(pid);
    i := i + 1;
  }
}

yield procedure {:layer 1} participant1 ({:linear_in "pid"} pid:int)
refines PARTICIPANT1;
requires {:layer 1} pid(pid);
{
  var v:vote;

  if (*)
  {
    call receive_req(pid);
    havoc v;
    call set_vote(pid, v);
    call send_vote(v);
  }
  async call participant2(pid);
}

yield procedure {:layer 1} participant2 ({:linear_in "pid"} pid:int)
refines PARTICIPANT2;
requires {:layer 1} pid(pid);
{
  var d:decision;

  call d := receive_decision(pid);
  call set_decision(pid, d);
}

yield invariant {:layer 1} YieldCoordinator();
invariant (forall vv:vote :: VoteChannel[vv] >= 0);

yield procedure {:layer 1} coordinator1 ({:linear_in "pid"} pid:int)
refines COORDINATOR1;
requires {:layer 1} pid == 0;
requires call YieldCoordinator();
{
  var i:int;
  var {:layer 1} old_RequestChannel:[int]int;

  call old_RequestChannel := Snapshot_RequestChannel();
  i := 1;
  while (i <= n)
  invariant {:layer 1} 1 <= i && i <= n+1;
  invariant {:layer 1} RequestChannel == (lambda ii:int :: if pid(ii) && ii < i then old_RequestChannel[ii] + 1 else old_RequestChannel[ii]);
  {
    call send_request(i);
    i := i + 1;
  }
  async call coordinator2(pid);
}

yield procedure {:layer 1} coordinator2 ({:linear_in "pid"} pid:int)
refines COORDINATOR2;
requires {:layer 1} pid == 0;
requires call YieldCoordinator();
{
  var d:decision;
  var v:vote;
  var i:int;
  var {:layer 1} old_VoteChannel:[vote]int;
  var {:layer 1} old_DecisionChannel:[int][decision]int;

  call old_VoteChannel := Snapshot_VoteChannel();
  call old_DecisionChannel := Snapshot_DecisionChannel();
  i := 0;
  d := COMMIT();
  while (i < n)
  invariant {:layer 1} 0 <= i && i <= n;
  invariant {:layer 1} VoteChannel[YES()] == old_VoteChannel[YES()] - i;
  invariant {:layer 1} old_VoteChannel[YES()] - i >= 0;
  invariant {:layer 1} VoteChannel[NO()] == old_VoteChannel[NO()];
  {
    call v := receive_vote();
    if (v == NO())
    {
      d := ABORT();
      break;
    }
    i := i + 1;
  }
  call set_decision(pid, d);
  i := 1;
  while (i <= n)
  invariant {:layer 1} 1 <= i && i <= n+1;
  invariant {:layer 1} DecisionChannel == (lambda ii:int :: (lambda dd:decision :: if pid(ii) && ii < i && dd == d then old_DecisionChannel[ii][dd] + 1 else old_DecisionChannel[ii][dd]));
  {
    call send_decision(i, d);
    i := i + 1;
  }
}

link action {:layer 1} Snapshot_RequestChannel() returns (snapshot:[int]int)
{
  snapshot := RequestChannel;
}

link action {:layer 1} Snapshot_VoteChannel() returns (snapshot:[vote]int)
{
  snapshot := VoteChannel;
}

link action {:layer 1} Snapshot_DecisionChannel() returns (snapshot:[int][decision]int)
{
  snapshot := DecisionChannel;
}

////////////////////////////////////////////////////////////////////////////////

<-> action {:layer 1} SET_VOTE({:linear "pid"} pid:int, v:vote)
modifies votes;
{
  votes[pid] := v;
}

<-> action {:layer 1} SET_DECISION({:linear "pid"} pid:int, d:decision)
modifies decisions;
{
  decisions[pid] := d;
}

<- action {:layer 1} SEND_REQUEST(pid:int)
modifies RequestChannel;
{
  RequestChannel[pid] := RequestChannel[pid] + 1;
}

-> action {:layer 1} RECEIVE_REQ(pid:int)
modifies RequestChannel;
{
  assume RequestChannel[pid] > 0;
  RequestChannel[pid] := RequestChannel[pid] - 1;
}

<- action {:layer 1} SEND_VOTE(v:vote)
modifies VoteChannel;
{
  VoteChannel[v] := VoteChannel[v] + 1;
}

-> action {:layer 1} RECEIVE_VOTE() returns (v:vote)
modifies VoteChannel;
{
  assume VoteChannel[v] > 0;
  VoteChannel[v] := VoteChannel[v] - 1;
}

<- action {:layer 1} SEND_DECISION(pid:int, d:decision)
modifies DecisionChannel;
{
  DecisionChannel[pid][d] := DecisionChannel[pid][d] + 1;
}

-> action {:layer 1} RECEIVE_DECISION(pid:int) returns (d:decision)
modifies DecisionChannel;
{
  assume DecisionChannel[pid][d] > 0;
  DecisionChannel[pid][d] := DecisionChannel[pid][d] - 1;
}

yield procedure {:layer 0} set_vote({:linear "pid"} pid:int, v:vote);
refines SET_VOTE;

yield procedure {:layer 0} set_decision({:linear "pid"} pid:int, d:decision);
refines SET_DECISION;

yield procedure {:layer 0} send_request(pid:int);
refines SEND_REQUEST;

yield procedure {:layer 0} receive_req(pid:int);
refines RECEIVE_REQ;

yield procedure {:layer 0} send_vote(v:vote);
refines SEND_VOTE;

yield procedure {:layer 0} receive_vote() returns (v:vote);
refines RECEIVE_VOTE;

yield procedure {:layer 0} send_decision(pid:int, d:decision);
refines SEND_DECISION;

yield procedure {:layer 0} receive_decision(pid:int) returns (d:decision);
refines RECEIVE_DECISION;

<-> action {:layer 1}
LINEAR_TRANSFER(i:int, {:linear_in "pid"} pids:[int]bool)
returns ({:linear "pid"} p:int, {:linear "pid"} pids':[int]bool)
{
  assert pids[i];
  p := i;
  pids' := pids[i := false];
}

yield procedure {:layer 0} linear_transfer(i:int, {:linear_in "pid"} pids:[int]bool)
returns ({:linear "pid"} p:int, {:linear "pid"} pids':[int]bool);
refines LINEAR_TRANSFER;
