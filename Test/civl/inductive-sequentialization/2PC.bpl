// RUN: %boogie -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A type for vote messages of participants
type {:datatype} vote;
function {:constructor} YES():vote;
function {:constructor} NO():vote;

// A type for decision message of the coordinator
type {:datatype} decision;
function {:constructor} COMMIT():decision;
function {:constructor} ABORT():decision;
function {:constructor} NONE():decision;

// Number of participants
const n:int;
axiom n > 0;

// Participants have IDs from 1 to n, and the coordinator has ID 0.
function {:inline} pid (pid:int) : bool { 1 <= pid && pid <= n }
function {:inline} pidLe (pid:int, k:int) : bool { 1 <= pid && pid <= k }
function {:inline} pidGt (pid:int, k:int) : bool { k < pid && pid <= n }

var {:layer 0,6} ReqCH:[int]int;           // Channel of the participants for request messages from the coordinator
var {:layer 0,6} DecCH:[int][decision]int; // Channel of the participants for decision messages from the coordinator
var {:layer 0,6} VoteCH:[vote]int;         // Channel of the coordinator for vote messages from the participants

var {:layer 0,6} votes:[int]vote;          // Participant votes
var {:layer 0,6} decisions:[int]decision;  // Coordinator and participant decisions

type {:pending_async}{:datatype} PA;
function {:pending_async "COORDINATOR1"}{:constructor} Coordinator1(pid:int) : PA;
function {:pending_async "COORDINATOR2"}{:constructor} Coordinator2(pid:int) : PA;
function {:pending_async "PARTICIPANT1"}{:constructor} Participant1(pid:int) : PA;
function {:pending_async "PARTICIPANT2"}{:constructor} Participant2(pid:int) : PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

function {:inline} SingletonPA (pa:PA) : [PA]int
{ NoPAs()[pa := 1] }

function {:builtin "MapAdd"} MapAddPA([PA]int, [PA]int) : [PA]int;

function trigger(x:int) : bool { true }

////////////////////////////////////////////////////////////////////////////////

function {:inline} Init(pids:[int]bool, ReqCH:[int]int, VoteCH:[vote]int,
  DecCH:[int][decision]int, decisions:[int]decision) : bool
{
  pids == MapConstBool(true) &&
  ReqCH == (lambda i:int :: 0) &&
  VoteCH == (lambda v:vote :: 0) &&
  DecCH == (lambda i:int :: (lambda d:decision :: 0)) &&
  decisions == (lambda i:int :: NONE())
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 6}
MAIN5 ({:linear_in "pid"} pids:[int]bool)
modifies ReqCH, VoteCH, votes, decisions;
{
  var dec:decision;
  assert Init(pids, ReqCH, VoteCH, DecCH, decisions);
  havoc ReqCH, VoteCH, votes, decisions;
  if (*) { dec := COMMIT(); } else { dec := ABORT(); }
  assume dec == COMMIT() ==> (forall i:int :: pid(i) ==> votes[i] == YES());
  assume (forall i:int :: (i == 0 || pid(i)) ==> decisions[i] == dec);
}

procedure {:IS_invariant}{:layer 5}
INV4 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "PARTICIPANT2"} PAs:[PA]int, {:choice} choice:PA)
modifies ReqCH, VoteCH, DecCH, votes, decisions;
{
  assert Init(pids, ReqCH, VoteCH, DecCH, decisions);

  havoc ReqCH, VoteCH, DecCH, votes, decisions;

  assume
  (exists k:int :: {trigger(k)} 0 <= k && k <= n && trigger(k+1) &&
    (decisions[0] == COMMIT() || decisions[0] == ABORT()) &&
    (decisions[0] == COMMIT() ==> (forall i:int :: pid(i) ==> votes[i] == YES())) &&
    (forall i:int :: pidLe(i,k) ==> decisions[i] == decisions[0]) &&
    DecCH == (lambda i:int :: (lambda d:decision :: if pidGt(i, k) && d == decisions[0] then 1 else 0)) &&
    PAs == (lambda pa:PA :: if is#Participant2(pa) && pidGt(pid#Participant2(pa), k) then 1 else 0) &&
    choice == Participant2(k+1) &&
    (k < n ==> PAs[Participant2(n)] > 0)
  );
}

procedure {:IS_abstraction}{:layer 5}
PARTICIPANT2' ({:linear_in "pid"} pid:int)
modifies VoteCH, DecCH, decisions;
{
  var d:decision;
  assert pid(pid);
  assert DecCH[pid][NONE()] == 0;
  assert DecCH[pid][COMMIT()] > 0 || DecCH[pid][ABORT()] > 0;
  if (*) { d := COMMIT(); } else { d := ABORT(); }
  assume DecCH[pid][d] > 0;
  DecCH[pid][d] := DecCH[pid][d] - 1;
  decisions[pid] := d;
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 5}
{:IS "MAIN5","INV4"}{:elim "PARTICIPANT2","PARTICIPANT2'"}
MAIN4 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "PARTICIPANT2"} PAs:[PA]int)
modifies ReqCH, VoteCH, DecCH, votes, decisions;
{
  var dec:decision;
  assert Init(pids, ReqCH, VoteCH, DecCH, decisions);
  assert trigger(0);
  havoc ReqCH, VoteCH, votes;
  if (*) { dec := COMMIT(); } else { dec := ABORT(); }
  assume dec == COMMIT() ==> (forall i:int :: pid(i) ==> votes[i] == YES());
  decisions[0] := dec;
  DecCH := (lambda i:int :: (lambda d:decision :: if pid(i) && d == dec then 1 else 0));
  PAs := (lambda pa:PA :: if is#Participant2(pa) && pid(pid#Participant2(pa)) then 1 else 0);
}

procedure {:IS_invariant}{:layer 4}
INV3 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "COORDINATOR2","PARTICIPANT2"} PAs:[PA]int)
modifies ReqCH, VoteCH, DecCH, votes, decisions;
{
  var dec:decision;
  assert Init(pids, ReqCH, VoteCH, DecCH, decisions);

  havoc ReqCH, VoteCH, votes;

  if (*)
  {
    assume VoteCH[YES()] >= 0 && VoteCH[NO()] >= 0;
    assume VoteCH[YES()] + VoteCH[NO()] <= n;
    assume VoteCH[YES()] == n ==> (forall i:int :: pid(i) ==> votes[i] == YES());
    PAs := MapAddPA(SingletonPA(Coordinator2(0)), (lambda pa:PA :: if is#Participant2(pa) && pid(pid#Participant2(pa)) then 1 else 0));
  }
  else
  {
    if (*) { dec := COMMIT(); } else { dec := ABORT(); }
    assume dec == COMMIT() ==> (forall i:int :: pid(i) ==> votes[i] == YES());
    decisions[0] := dec;
    DecCH := (lambda i:int :: (lambda d:decision :: if pid(i) && d == dec then 1 else 0));
    PAs := (lambda pa:PA :: if is#Participant2(pa) && pid(pid#Participant2(pa)) then 1 else 0);
  }
}

procedure {:IS_abstraction}{:layer 4}
COORDINATOR2' ({:linear_in "pid"} pid:int)
modifies VoteCH, DecCH, decisions;
{
  var dec:decision;
  assert pid == 0;

  if (*)
  {
    assume VoteCH[YES()] >= n;
    dec := COMMIT();
  }
  else
  {
    dec := ABORT();
  }

  decisions[pid] := dec;
  havoc VoteCH;
  DecCH := (lambda i:int :: (lambda d:decision :: if pid(i) && d == dec then DecCH[i][d] + 1 else DecCH[i][d]));
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 4}
{:IS "MAIN4","INV3"}{:elim "COORDINATOR2","COORDINATOR2'"}
MAIN3 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "COORDINATOR2","PARTICIPANT2"} PAs:[PA]int)
modifies ReqCH, VoteCH, votes;
{
  assert Init(pids, ReqCH, VoteCH, DecCH, decisions);
  havoc ReqCH, VoteCH, votes;
  assume VoteCH[YES()] >= 0 && VoteCH[NO()] >= 0;
  assume VoteCH[YES()] + VoteCH[NO()] <= n;
  assume VoteCH[YES()] == n ==> (forall i:int :: pid(i) ==> votes[i] == YES());
  PAs := MapAddPA(SingletonPA(Coordinator2(0)), (lambda pa:PA :: if is#Participant2(pa) && pid(pid#Participant2(pa)) then 1 else 0));
}

procedure {:IS_invariant}{:layer 3}
INV2 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "COORDINATOR2","PARTICIPANT1","PARTICIPANT2"} PAs:[PA]int, {:choice} choice:PA)
modifies ReqCH, VoteCH, votes;
{
  assert Init(pids, ReqCH, VoteCH, DecCH, decisions);

  havoc ReqCH, VoteCH, votes;

  assume
  (exists k:int :: {trigger(k)} 0 <= k && k <= n && trigger(k+1) &&
    (forall i:int :: pidGt(i,k) ==> ReqCH[i] == 1) &&
    VoteCH[YES()] >= 0 && VoteCH[NO()] >= 0 &&
    VoteCH[YES()] + VoteCH[NO()] <= k &&
    (VoteCH[YES()] == k ==> (forall i:int :: pidLe(i,k) ==> votes[i] == YES())) &&
    PAs == MapAddPA(SingletonPA(Coordinator2(0)),
      MapAddPA((lambda pa:PA :: if is#Participant2(pa) && pidLe(pid#Participant2(pa), k) then 1 else 0),
               (lambda pa:PA :: if is#Participant1(pa) && pidGt(pid#Participant1(pa), k) then 1 else 0))) &&
    choice == Participant1(k+1) &&
    (k < n ==> PAs[Participant1(n)] > 0)
  );
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 3}
{:IS "MAIN3","INV2"}{:elim "PARTICIPANT1"}
MAIN2 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "COORDINATOR2","PARTICIPANT1"} PAs:[PA]int)
modifies ReqCH;
{
  assert Init(pids, ReqCH, VoteCH, DecCH, decisions);
  assert trigger(0);
  ReqCH := (lambda i:int :: if pid(i) then 1 else 0);
  PAs := MapAddPA(SingletonPA(Coordinator2(0)), (lambda pa:PA :: if is#Participant1(pa) && pid(pid#Participant1(pa)) then 1 else 0));
}

procedure {:IS_invariant}{:layer 2}
INV1 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "COORDINATOR1","COORDINATOR2","PARTICIPANT1"} PAs:[PA]int)
modifies ReqCH;
{
  assert Init(pids, ReqCH, VoteCH, DecCH, decisions);
  if (*)
  {
    PAs := MapAddPA(SingletonPA(Coordinator1(0)), (lambda pa:PA :: if is#Participant1(pa) && pid(pid#Participant1(pa)) then 1 else 0));
    assume PAs[Coordinator1(0)] > 0;
  }
  else
  {
    ReqCH := (lambda i:int :: if pid(i) then 1 else 0);
    PAs := MapAddPA(SingletonPA(Coordinator2(0)), (lambda pa:PA :: if is#Participant1(pa) && pid(pid#Participant1(pa)) then 1 else 0));
    assume (forall pa:PA :: PAs[pa] == 0 <== is#Coordinator1(pa));
    assume PAs[Coordinator2(0)] == 1;
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}
{:IS "MAIN2","INV1"}{:elim "COORDINATOR1"}
MAIN1 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "COORDINATOR1","PARTICIPANT1"} PAs:[PA]int)
{
  assert Init(pids, ReqCH, VoteCH, DecCH, decisions);
  PAs := MapAddPA(SingletonPA(Coordinator1(0)), (lambda pa:PA :: if is#Participant1(pa) && pid(pid#Participant1(pa)) then 1 else 0));
}

procedure {:atomic}{:layer 2,3}
PARTICIPANT1 ({:linear_in "pid"} pid:int)
returns ({:pending_async "PARTICIPANT2"} PAs:[PA]int)
modifies ReqCH, VoteCH, votes;
{
  var v:vote;
  assert pid(pid);

  if (*)
  {
    assume ReqCH[pid] > 0;
    ReqCH[pid] := ReqCH[pid] - 1;
    if (*) { v := YES(); } else { v := NO(); }
    votes[pid] := v;
    VoteCH[v] := VoteCH[v] + 1;
  }

  PAs := SingletonPA(Participant2(pid));
}

procedure {:atomic}{:layer 2,5}
PARTICIPANT2 ({:linear_in "pid"} pid:int)
modifies DecCH, decisions;
{
  var d:decision;
  assert pid(pid);
  assert DecCH[pid][NONE()] == 0;
  if (*) { d := COMMIT(); } else { d := ABORT(); }
  assume DecCH[pid][d] > 0;
  DecCH[pid][d] := DecCH[pid][d] - 1;
  decisions[pid] := d;
}

procedure {:left}{:layer 2}
COORDINATOR1 ({:linear_in "pid"} pid:int)
returns ({:pending_async "COORDINATOR2"} PAs:[PA]int)
modifies ReqCH;
{
  assert pid == 0;
  ReqCH := (lambda i:int :: if pid(i) then ReqCH[i] + 1 else ReqCH[i]);
  PAs := SingletonPA(Coordinator2(0));
}

procedure {:atomic}{:layer 2,4}
COORDINATOR2 ({:linear_in "pid"} pid:int)
modifies VoteCH, DecCH, decisions;
{
  var dec:decision;
  assert pid == 0;

  if (*)
  {
    assume VoteCH[YES()] >= n;
    VoteCH[YES()] := VoteCH[YES()] - n;
    dec := COMMIT();
  }
  else
  {
    assume VoteCH[NO()] > 0;
    havoc VoteCH;
    assume VoteCH[NO()] == old(VoteCH)[NO()] - 1;
    assume 0 <= VoteCH[YES()] && VoteCH[YES()] <= old(VoteCH)[YES()];
    dec := ABORT();
  }

  decisions[pid] := dec;
  DecCH := (lambda i:int :: (lambda d:decision :: if pid(i) && d == dec then DecCH[i][d] + 1 else DecCH[i][d]));
}

////////////////////////////////////////////////////////////////////////////////

procedure {:yields}{:layer 1}{:refines "MAIN1"}
main ({:linear_in "pid"} pids:[int]bool)
requires {:layer 1} Init(pids, ReqCH, VoteCH, DecCH, decisions);
{
  var i:int;
  var {:pending_async}{:layer 1} PAs:[PA]int;
  var {:linear "pid"} pid:int;
  var {:linear "pid"} pids':[int]bool;
  yield; assert {:layer 1} Init(pids, ReqCH, VoteCH, DecCH, decisions);
  pids' := pids;
  call pid, pids' := linear_transfer(0, pids');
  async call coordinator1(pid);
  i := 1;
  while (i <= n)
  invariant {:layer 0,1}{:terminates} true;
  invariant {:layer 1} 1 <= i && i <= n+1;
  invariant {:layer 1} (forall ii:int :: pid(ii) && ii >= i ==> pids'[ii]);
  invariant {:layer 1} PAs == MapAddPA(SingletonPA(Coordinator1(0)), (lambda pa:PA :: if is#Participant1(pa) && pid(pid#Participant1(pa)) && pid#Participant1(pa) < i then 1 else 0));
  {
    call pid, pids' := linear_transfer(i, pids');
    async call participant1(pid);
    i := i + 1;
  }
  yield;
}

procedure {:yields}{:layer 1}{:refines "PARTICIPANT1"}
participant1 ({:linear_in "pid"} pid:int)
requires {:layer 1} pid(pid);
{
  var v:vote;
  yield;
  if (*)
  {
    call receive_req(pid);
    havoc v;
    call set_vote(pid, v);
    call send_vote(v);
  }
  async call participant2(pid);
  yield;
}

procedure {:yields}{:layer 1}{:refines "PARTICIPANT2"}
participant2 ({:linear_in "pid"} pid:int)
requires {:layer 1} pid(pid);
{
  var d:decision;
  yield;
  call d := receive_dec(pid);
  call set_decision(pid, d);
  yield;
}

procedure {:yields}{:layer 1}{:refines "COORDINATOR1"}
coordinator1 ({:linear_in "pid"} pid:int)
requires {:layer 1} pid == 0;
requires {:layer 1} (forall vv:vote :: VoteCH[vv] >= 0);
{
  var i:int;
  var {:layer 1} old_ReqCH:[int]int;
  yield;
  assert {:layer 1} (forall vv:vote :: VoteCH[vv] >= 0);
  call old_ReqCH := Snapshot_ReqCH();
  i := 1;
  while (i <= n)
  invariant {:layer 1}{:terminates} true;
  invariant {:layer 1} 1 <= i && i <= n+1;
  invariant {:layer 1} ReqCH == (lambda ii:int :: if pid(ii) && ii < i then old_ReqCH[ii] + 1 else old_ReqCH[ii]);
  {
    call send_req(i);
    i := i + 1;
  }
  async call coordinator2(pid);
  yield;
}

procedure {:yields}{:layer 1}{:refines "COORDINATOR2"}
coordinator2 ({:linear_in "pid"} pid:int)
requires {:layer 1} pid == 0;
requires {:layer 1} (forall vv:vote :: VoteCH[vv] >= 0);
{
  var d:decision;
  var v:vote;
  var i:int;
  var {:layer 1} old_VoteCH:[vote]int;
  var {:layer 1} old_DecCH:[int][decision]int;
  yield;
  assert {:layer 1} (forall vv:vote :: VoteCH[vv] >= 0);
  call old_VoteCH := Snapshot_VoteCH();
  call old_DecCH := Snapshot_DecCH();
  i := 0;
  d := COMMIT();
  while (i < n)
  invariant {:layer 1} 0 <= i && i <= n;
  invariant {:layer 1} VoteCH[YES()] == old_VoteCH[YES()] - i;
  invariant {:layer 1} old_VoteCH[YES()] - i >= 0;
  invariant {:layer 1} VoteCH[NO()] == old_VoteCH[NO()];
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
  invariant {:layer 1}{:terminates} true;
  invariant {:layer 1} 1 <= i && i <= n+1;
  invariant {:layer 1} DecCH == (lambda ii:int :: (lambda dd:decision :: if pid(ii) && ii < i && dd == d then old_DecCH[ii][dd] + 1 else old_DecCH[ii][dd]));
  {
    call send_dec(i, d);
    i := i + 1;
  }
  yield;
}

procedure {:intro}{:layer 1} Snapshot_ReqCH() returns (snapshot:[int]int)
{
  snapshot := ReqCH;
}

procedure {:intro}{:layer 1} Snapshot_VoteCH() returns (snapshot:[vote]int)
{
  snapshot := VoteCH;
}

procedure {:intro}{:layer 1} Snapshot_DecCH() returns (snapshot:[int][decision]int)
{
  snapshot := DecCH;
}

////////////////////////////////////////////////////////////////////////////////

procedure {:both}{:layer 1} SET_VOTE({:linear "pid"} pid:int, v:vote)
modifies votes;
{
  votes[pid] := v;
}

procedure {:both}{:layer 1} SET_DECISION({:linear "pid"} pid:int, d:decision)
modifies decisions;
{
  decisions[pid] := d;
}

procedure {:left}{:layer 1} SEND_REQ(pid:int)
modifies ReqCH;
{
  ReqCH[pid] := ReqCH[pid] + 1;
}

procedure {:right}{:layer 1} RECEIVE_REQ(pid:int)
modifies ReqCH;
{
  assume ReqCH[pid] > 0;
  ReqCH[pid] := ReqCH[pid] - 1;
}

procedure {:left}{:layer 1} SEND_VOTE(v:vote)
modifies VoteCH;
{
  VoteCH[v] := VoteCH[v] + 1;
}

procedure {:right}{:layer 1} RECEIVE_VOTE() returns (v:vote)
modifies VoteCH;
{
  assume VoteCH[v] > 0;
  VoteCH[v] := VoteCH[v] - 1;
}

procedure {:left}{:layer 1} SEND_DEC(pid:int, d:decision)
modifies DecCH;
{
  DecCH[pid][d] := DecCH[pid][d] + 1;
}

procedure {:right}{:layer 1} RECEIVE_DEC(pid:int) returns (d:decision)
modifies DecCH;
{
  assume DecCH[pid][d] > 0;
  DecCH[pid][d] := DecCH[pid][d] - 1;
}

procedure {:yields}{:layer 0}{:refines "SET_VOTE"} set_vote({:linear "pid"} pid:int, v:vote);
procedure {:yields}{:layer 0}{:refines "SET_DECISION"} set_decision({:linear "pid"} pid:int, d:decision);
procedure {:yields}{:layer 0}{:refines "SEND_REQ"} send_req(pid:int);
procedure {:yields}{:layer 0}{:refines "RECEIVE_REQ"} receive_req(pid:int);
procedure {:yields}{:layer 0}{:refines "SEND_VOTE"} send_vote(v:vote);
procedure {:yields}{:layer 0}{:refines "RECEIVE_VOTE"} receive_vote() returns (v:vote);
procedure {:yields}{:layer 0}{:refines "SEND_DEC"} send_dec(pid:int, d:decision);
procedure {:yields}{:layer 0}{:refines "RECEIVE_DEC"} receive_dec(pid:int) returns (d:decision);

procedure {:both}{:layer 1}
LINEAR_TRANSFER(i:int, {:linear_in "pid"} pids:[int]bool)
returns ({:linear "pid"} p:int, {:linear "pid"} pids':[int]bool)
{
  assert pids[i];
  p := i;
  pids' := pids[i := false];
}

procedure {:yields}{:layer 0}{:refines "LINEAR_TRANSFER"} linear_transfer(i:int, {:linear_in "pid"} pids:[int]bool)
returns ({:linear "pid"} p:int, {:linear "pid"} pids':[int]bool);

////////////////////////////////////////////////////////////////////////////////

function {:builtin "MapConst"} MapConstBool (bool) : [int]bool;
function {:builtin "MapOr"} MapOr ([int]bool, [int]bool) : [int]bool;

function {:inline}{:linear "pid"} PidCollector (pid:int) : [int]bool
{
  MapConstBool(false)[pid := true]
}

function {:inline}{:linear "pid"} PidSetCollector (pids:[int]bool) : [int]bool
{
  pids
}
