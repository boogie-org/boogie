// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Pid = int;
const n:int;
axiom n >= 1;

var {:layer 0,4} channel:[int][int]int;  // (pid x msg) -> count
var {:layer 1,4} terminated:[int]bool;   // Ghost var to keep terminated node info
var {:layer 0,4} id:[int]int;            // pid -> ID
var {:layer 0,4} leader:[int]bool;       // leader[pid] iff pid is a leader

function {:inline} Pid (pid:int) : bool { 1 <= pid && pid <= n }

function {:inline} Next (pid:int) : int { if pid < n then pid + 1 else 1 }
function {:inline} Prev (pid:int) : int { if pid > 1 then pid - 1 else n }

// True iff b is between a and c in a ring, excluding the boundaries
// Between relation is assumed to be growing such that when a == c, every b in the ring is between a and c
function {:inline} Between (a:int, b:int, c:int) : bool
{
  Pid(a) && Pid(b) && Pid(c) &&
  (
    (a < b && b < c) ||
    (c < a && a < b) ||
    (b < c && c < a) ||
    (a == c && a != b)
  )
}

// True iff b is between a and c excluding only c
// Between relation is assumed to be growing such that when a == c, every b in the ring is between a and c
function {:inline} BetweenLeftEqual (a:int, b:int, c:int) : bool
{
  Pid(a) && Pid(b) && Pid(c) &&
  (
    (a <= b && b < c) ||
    (c < a && a <= b) ||
    (b < c && c < a)
  )
}

// Returns pid with maximum id number
function Max ([int]int) : int;
axiom (forall id:[int]int :: Pid(Max(id)) && (forall i:int :: Pid(i) && i != Max(id) ==> id[i] < id[Max(id)]));

function EmptyChannel() : [int]int { (lambda i:int :: 0) }

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

atomic action {:layer 4} MAIN3 ({:linear_in} pids: Set int)
modifies channel, terminated, leader;
{
  assert Init(pids->val, channel, terminated, id, leader);
  havoc channel, terminated, leader;
  assume (forall i:int :: Pid(i) && i != Max(id) ==> !leader[i]);
}

action {:layer 3}
INV2 ({:linear_in} pids: Set int)
creates P;
modifies channel, terminated, leader;
{
  var {:pool "INV2"} k: int;
  assert Init(pids->val, channel, terminated, id, leader);

  havoc channel, terminated, leader;
  assume {:add_to_pool "INV2", k, Next(k), n+1} true;
  if (*) {
    assume
      Pid(k) &&
      (forall i:int :: Pid(i) && Between(Max(id),i,k) ==> terminated[i]) &&
      (forall i:int :: Pid(i) && !Between(Max(id),i,k) ==> !terminated[i]);
    call create_asyncs((lambda pa:P :: Pid(pa->pid->val) && !Between(Max(id), pa->pid->val, k)));
    call set_choice(P(One(k)));
  } else {
    assume
      k == n + 1 &&
      (forall i:int :: Pid(i) ==> terminated[i]);
  }

  assume (forall i:int, msg:int :: Pid(i) && channel[i][msg] > 0 ==> msg <= id[Max(id)] && (forall j:int:: BetweenLeftEqual(i,j,Max(id)) ==> msg != id[j]));
  assume (forall i:int :: Pid(i) && i != Max(id) ==> !leader[i]);
}

action {:layer 3} P' ({:linear_in} pid: One int)
creates P;
modifies channel, terminated, leader;
{
  assert (forall j:int :: Pid(j) && Between(Max(id), j, pid->val) ==> terminated[j]);
  call P(pid);
}

////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 3} MAIN2 ({:linear_in} pids: Set int)
refines MAIN3 using INV2;
creates P;
eliminates P using P';
modifies channel;
{
  assert Init(pids->val, channel, terminated, id, leader);

  assume {:add_to_pool "INV2", Next(Max(id))} true;
  havoc channel;
  assume (forall i:int :: 1 <= i && i <= n ==> channel[Next(i)] == EmptyChannel()[id[i] := 1 ]);
  assume (forall i:int :: i < 1  || i > n ==> channel[i] == EmptyChannel());
  call create_asyncs((lambda pa:P :: Pid(pa->pid->val)));
  assume (forall i:int, msg:int :: Pid(i) && channel[i][msg] > 0 ==> msg == id[Prev(i)]);
}

action {:layer 2}
INV1 ({:linear_in} pids: Set int)
creates PInit, P;
modifies channel;
{
  var {:pool "INV1"} k: int;
  assert Init(pids->val, channel, terminated, id, leader);

  havoc channel;
  assume
    {:add_to_pool "INV1", k+1}
    {:add_to_pool "PInit", PInit(One(n))}
    {:add_to_pool "CHANNEL_INV", k+1}
    Pid(k) || k == 0;
  assume (forall {:pool "CHANNEL_INV"} i:int :: {:add_to_pool "CHANNEL_INV", i} 1 <= i && i <= k ==> channel[Next(i)] == EmptyChannel()[id[i] := 1]);
  assume (forall {:pool "CHANNEL_INV"} i:int :: {:add_to_pool "CHANNEL_INV", i} k < i && i <= n ==> channel[Next(i)] == EmptyChannel());
  assume (forall i:int :: i < 1  || i > n ==> channel[i] == EmptyChannel());
  call create_asyncs((lambda {:pool "PInit"} pa:PInit :: k < pa->pid->val && pa->pid->val <= n));
  call create_asyncs((lambda pa:P :: 1 <= pa->pid->val && pa->pid->val <= k));
  call set_choice(PInit(One(k+1)));
}

////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 2} MAIN1 ({:linear_in} pids: Set int)
refines MAIN2 using INV1;
creates PInit;
{
  assert Init(pids->val, channel, terminated, id, leader);

  assume {:add_to_pool "INV1", 0} true;
  call create_asyncs((lambda pa:PInit :: Pid(pa->pid->val)));
}

async left action {:layer 2} PInit ({:linear_in} pid: One int)
creates P;
modifies channel;
{
  assert Pid(pid->val);
  channel[Next(pid->val)][id[pid->val]] := channel[Next(pid->val)][id[pid->val]] + 1;
  call create_async(P(pid));
}

async atomic action {:layer 2, 3} P ({:linear_in} pid: One int)
creates P;
modifies channel, terminated, leader;
{
  var msg:int;

  assert Pid(pid->val);
  assert !terminated[pid->val];
  assert (forall m:int :: channel[pid->val][m] > 0 ==> m <= id[Max(id)]);

  if (*)
  {
    terminated[pid->val] := true;
  }
  else
  {
    assume channel[pid->val][msg] > 0;
    channel[pid->val][msg] := channel[pid->val][msg] - 1;

    if (msg == id[pid->val])
    {
      leader[pid->val] := true;
      terminated[pid->val] := true;
    }
    else
    {
      if (msg > id[pid->val])
      {
        channel[Next(pid->val)][msg] := channel[Next(pid->val)][msg] + 1;
      }
      call create_async(P(pid));
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 1} YieldInit({:linear} pids: Set int);
invariant Init(pids->val, channel, terminated, id, leader);

yield procedure {:layer 1}
main ({:linear_in} pids: Set int)
refines MAIN1;
requires call YieldInit(pids);
{
  var {:pending_async}{:layer 1} PAs:[PInit]int;
  var {:linear} pid: One int;
  var {:linear} pids': Set int;
  var i:int;

  pids' := pids;
  i := 1;
  while (i <= n)
  invariant {:layer 1} 1 <= i && i <= n+1;
  invariant {:layer 1} (forall ii:int :: Pid(ii) && ii >= i ==> Set_Contains(pids', ii));
  invariant {:layer 1} PAs == (lambda pa:PInit :: if Pid(pa->pid->val) && pa->pid->val < i then 1 else 0);
  {
    call pid := One_Get(pids', i);
    async call pinit(pid);
    i := i + 1;
  }
}

yield procedure {:layer 1} pinit ({:linear_in} pid: One int)
refines PInit;
requires {:layer 1} Pid(pid->val);
{
  var m:int;

  call m := get_id(pid);
  call send(Next(pid->val), m);
  async call p(pid);
}

yield procedure {:layer 1} p ({:linear_in} pid: One int)
refines P;
requires {:layer 1} Pid(pid->val);
{
  var m:int;
  var i:int;

  call i := get_id(pid);
  call m := receive(pid->val);
  if (m == i)
  {
    call set_leader(pid);
    call {:layer 1} terminated := set_terminated(terminated, pid->val);
  }
  else
  {
    if (m > i)
    {
      call send(Next(pid->val), m);
    }
    async call p(pid);
  }
}

pure procedure {:inline 1} set_terminated(terminated:[int]bool, pid:int) returns (terminated':[int]bool)
{
  terminated' := terminated[pid := true];
}

////////////////////////////////////////////////////////////////////////////////

both action {:layer 1} GET_ID({:linear} pid: One int) returns (i:int)
{
  i := id[pid->val];
}

both action {:layer 1} SET_LEADER({:linear} pid: One int)
modifies leader;
{
  leader[pid->val] := true;
}

left action {:layer 1} SEND(pid:int, m:int)
modifies channel;
{
  channel[pid][m] := channel[pid][m] + 1;
}

right action {:layer 1} RECEIVE(pid:int) returns (m:int)
modifies channel;
{
  assume channel[pid][m] > 0;
  channel[pid][m] := channel[pid][m] - 1;
}

yield procedure {:layer 0} get_id({:linear} pid: One int) returns (i:int);
refines GET_ID;

yield procedure {:layer 0} set_leader({:linear} pid: One int);
refines SET_LEADER;

yield procedure {:layer 0} send(pid:int, m:int);
refines SEND;

yield procedure {:layer 0} receive(pid:int) returns (m:int);
refines RECEIVE;
