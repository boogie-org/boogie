// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "pid"} Pid = int;
const n:int;
axiom n >= 1;

var {:layer 0,4} channel:[int][int]int;  // (pid x msg) -> count
var {:layer 1,4} terminated:[int]bool;   // Ghost var to keep terminated node info
var {:layer 0,4} id:[int]int;            // pid -> ID
var {:layer 0,4} leader:[int]bool;       // leader[pid] iff pid is a leader

function {:inline} pid (pid:int) : bool { 1 <= pid && pid <= n }

function {:inline} next (pid:int) : int { if pid < n then pid + 1 else 1 }
function {:inline} prev (pid:int) : int { if pid > 1 then pid - 1 else n }

// True iff b is between a and c in a ring, excluding the boundaries
// Between relation is assumed to be growing such that when a == c, every b in the ring is between a and c
function {:inline} between (a:int, b:int, c:int) : bool
{
  pid(a) && pid(b) && pid(c) &&
  (
    (a < b && b < c) ||
    (c < a && a < b) ||
    (b < c && c < a) ||
    (a == c && a != b)
  )
}

// True iff b is between a and c excluding only c
// Between relation is assumed to be growing such that when a == c, every b in the ring is between a and c
function {:inline} betweenLeftEqual (a:int, b:int, c:int) : bool
{
  pid(a) && pid(b) && pid(c) &&
  (
    (a <= b && b < c) ||
    (c < a && a <= b) ||
    (b < c && c < a)
  )
}

// Returns pid with maximum id number
function max ([int]int) : int;
axiom (forall id:[int]int :: pid(max(id)) && (forall i:int :: pid(i) && i != max(id) ==> id[i] < id[max(id)]));

// A type for keeping track of pending asyncs
type {:pending_async}{:datatype} PA;
function {:constructor} P(pid:int) : PA;
function {:constructor} PInit(pid:int) : PA;

// A dummy trigger function to use in quantified formulae
function trigger(x:int) : bool { true }

function EmptyChannel() : [int]int { (lambda i:int :: 0) }
function NoPAs() : [PA]int { (lambda pa:PA :: 0) }

////////////////////////////////////////////////////////////////////////////////

function {:inline} Init(pids:[int]bool, channel:[int][int]int,
  terminated:[int]bool, id:[int]int, leader:[int]bool) : bool
{
  pids == MapConst(true) &&
  channel == (lambda i:int :: EmptyChannel()) &&
  terminated == (lambda i:int :: false) &&
  leader == (lambda i:int :: false) &&
  (forall i:int, j:int :: id[i] == id[j] ==> i == j)
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 4}
MAIN3 ({:linear_in "pid"} pids:[int]bool)
returns ()
modifies channel, terminated, leader;
{
  assert Init(pids, channel, terminated, id, leader);
  havoc channel, terminated, leader;
  assume (forall i:int :: pid(i) && i != max(id) ==> !leader[i]);
}

procedure {:IS_invariant}{:layer 3}
INV2 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "P"} PAs:[PA]int, {:choice} choice:PA)
modifies channel, terminated, leader;
{
  assert Init(pids, channel, terminated, id, leader);

  havoc channel, terminated, leader;

  assume
  (exists k:int :: {trigger(k)} trigger(k) && trigger(next(k)) && trigger(n+1) &&
    choice == P(k) &&
    //(k == next(max(id)) ==> (forall i:int, msg:int :: pid(i) && channel[i][msg] > 0 ==> msg == id[prev(i)])) &&  // A helper to the prover for the base case of IS
    (
      (pid(k) &&
       (forall i:int :: pid(i) && between(max(id),i,k) ==> terminated[i]) &&
       (forall i:int :: pid(i) && !between(max(id),i,k) ==> !terminated[i]) &&
       PAs == (lambda pa:PA :: if is#P(pa) && pid(pid#P(pa)) && !between(max(id), pid#P(pa), k) then 1 else 0))
      ||
      (k == n + 1 &&
       (forall i:int :: pid(i) ==> terminated[i]) &&
       PAs == NoPAs()
      )
    )
  );

  assume (forall i:int, msg:int :: pid(i) && channel[i][msg] > 0 ==> msg <= id[max(id)] && (forall j:int:: betweenLeftEqual(i,j,max(id)) ==> msg != id[j]));
  assume (forall i:int :: pid(i) && i != max(id) ==> !leader[i]);
}

procedure {:IS_abstraction}{:layer 3}
P' ({:linear_in "pid"} pid:int)
returns ({:pending_async "P"} PAs:[PA]int)
modifies channel, terminated, leader;
{
  var msg:int;

  assert pid(pid);
  assert !terminated[pid];
  assert (forall m:int :: channel[pid][m] > 0 ==> m <= id[max(id)]);

  assert (forall j:int :: pid(j) && between(max(id), j, pid) ==> terminated[j]);

  if (*)
  {
    terminated[pid] := true;
    PAs := NoPAs();
  }
  else
  {
    assume channel[pid][msg] > 0;
    channel[pid][msg] := channel[pid][msg] - 1;

    if (msg == id[pid])
    {
      leader[pid] := true;
      terminated[pid] := true;
      PAs := NoPAs();
    }
    else
    {
      if (msg > id[pid])
      {
        channel[next(pid)][msg] := channel[next(pid)][msg] + 1;
      }
      PAs := NoPAs()[P(pid) := 1];
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 3}
{:IS "MAIN3","INV2"}{:elim "P", "P'" }
MAIN2 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "P"} PAs:[PA]int)
modifies channel;
{
  assert Init(pids, channel, terminated, id, leader);
  assert trigger(next(max(id)));

  havoc channel;

  assume (forall i:int :: 1 <= i && i <= n ==> channel[next(i)] == EmptyChannel()[id[i] := 1 ]);
  assume (forall i:int :: i < 1  || i > n ==> channel[i] == EmptyChannel());
  PAs := (lambda pa:PA ::  if is#P(pa) && pid(pid#P(pa)) then 1 else 0);
  assume (forall i:int, msg:int :: pid(i) && channel[i][msg] > 0 ==> msg == id[prev(i)]);
}

procedure {:IS_invariant}{:layer 2}
INV1 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "PInit", "P"} PAs:[PA]int, {:choice} choice:PA)
modifies channel;
{
  assert Init(pids, channel, terminated, id, leader);

  havoc channel;

  assume
  (exists k:int :: {trigger(k)} (pid(k) || k == 0) && trigger(k+1) &&
    (forall i:int :: 1 <= i && i <= k ==> channel[next(i)] == EmptyChannel()[id[i] := 1 ]) &&
    (forall i:int :: k < i && i <= n ==> channel[next(i)] == EmptyChannel()) &&
    (forall i:int :: i < 1  || i > n ==> channel[i] == EmptyChannel()) &&
    PAs == (lambda pa:PA :: if is#PInit(pa) && k < pid#PInit(pa) && pid#PInit(pa) <= n then 1
              else if is#P(pa) &&  1 <= pid#P(pa) && pid#P(pa) <= k  then 1 else 0) &&
    choice == PInit(k+1) &&
    (k < n ==> PAs[PInit(n)] > 0)   // Hint for the prover for the conclusion check
  );
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}
{:IS "MAIN2","INV1"}{:elim "PInit"}
MAIN1 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "PInit"} PAs:[PA]int)
{
  assert Init(pids, channel, terminated, id, leader);
  assert trigger(0);
  PAs := (lambda pa:PA :: if is#PInit(pa) && pid(pid#PInit(pa)) then 1 else 0);
}

procedure {:left}{:layer 2}
PInit ({:linear_in "pid"} pid:int)
returns ({:pending_async "P"} PAs:[PA]int)
modifies channel;
{
  assert pid(pid);
  channel[next(pid)][id[pid]] := channel[next(pid)][id[pid]] + 1;
  PAs := NoPAs()[P(pid) := 1];
}

procedure {:atomic}{:layer 2, 3}
P ({:linear_in "pid"} pid:int)
returns ({:pending_async "P"} PAs:[PA]int)
modifies channel, terminated, leader;
{
  var msg:int;

  assert pid(pid);
  assert !terminated[pid];
  assert (forall m:int :: channel[pid][m] > 0 ==> m <= id[max(id)]);

  if (*)
  {
    terminated[pid] := true;
    PAs := NoPAs();
  }
  else
  {
    assume trigger(msg); // Hack for commutativity checking. Replace with proper witness feature!
    assume channel[pid][msg] > 0;
    channel[pid][msg] := channel[pid][msg] - 1;

    if (msg == id[pid])
    {
      leader[pid] := true;
      terminated[pid] := true;
      PAs := NoPAs();
    }
    else
    {
      if (msg > id[pid])
      {
        channel[next(pid)][msg] := channel[next(pid)][msg] + 1;
      }
      PAs := NoPAs()[P(pid) := 1];
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:yields}{:layer 1}{:refines "MAIN1"}
main ({:linear_in "pid"} pids:[int]bool)
requires {:layer 1} Init(pids, channel, terminated, id, leader);
{
  var {:pending_async}{:layer 1} PAs:[PA]int;
  var {:linear "pid"} pid:int;
  var {:linear "pid"} pids':[int]bool;
  var i:int;

  pids' := pids;
  i := 1;
  while (i <= n)
  invariant {:layer 1}{:cooperates} true;
  invariant {:layer 1} 1 <= i && i <= n+1;
  invariant {:layer 1} (forall ii:int :: pid(ii) && ii >= i ==> pids'[ii]);
  invariant {:layer 1} PAs == (lambda pa:PA :: if is#PInit(pa) && pid(pid#PInit(pa)) && pid#PInit(pa) < i then 1 else 0);
  {
    call pid, pids' := linear_transfer(i, pids');
    async call pinit(pid);
    i := i + 1;
  }
}

procedure {:yields}{:layer 1}{:refines "PInit"}
pinit ({:linear_in "pid"} pid:int)
requires {:layer 1} pid(pid);
{
  var m:int;

  call m := get_id(pid);
  call send(next(pid), m);
  async call p(pid);
}

procedure {:yields}{:layer 1}{:refines "P"}
p ({:linear_in "pid"} pid:int)
requires {:layer 1} pid(pid);
{
  var m:int;
  var i:int;

  call i := get_id(pid);
  call m := receive(pid);
  if (m == i)
  {
    call set_leader(pid);
    call set_terminated(pid);
  }
  else
  {
    if (m > i)
    {
      call send(next(pid), m);
    }
    async call p(pid);
  }
}

procedure {:intro}{:layer 1} set_terminated(pid:int)
modifies terminated;
{
  terminated[pid] := true;
}

////////////////////////////////////////////////////////////////////////////////

procedure {:both}{:layer 1} GET_ID({:linear "pid"} pid:int) returns (i:int)
{
  i := id[pid];
}

procedure {:both}{:layer 1} SET_LEADER({:linear "pid"} pid:int)
modifies leader;
{
  leader[pid] := true;
}

procedure {:left}{:layer 1} SEND(pid:int, m:int)
modifies channel;
{
  channel[pid][m] := channel[pid][m] + 1;
}

procedure {:right}{:layer 1} RECEIVE(pid:int) returns (m:int)
modifies channel;
{
  assume channel[pid][m] > 0;
  channel[pid][m] := channel[pid][m] - 1;
}

procedure {:yields}{:layer 0}{:refines "GET_ID"} get_id({:linear "pid"} pid:int) returns (i:int);
procedure {:yields}{:layer 0}{:refines "SET_LEADER"} set_leader({:linear "pid"} pid:int);
procedure {:yields}{:layer 0}{:refines "SEND"} send(pid:int, m:int);
procedure {:yields}{:layer 0}{:refines "RECEIVE"} receive(pid:int) returns (m:int);

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
