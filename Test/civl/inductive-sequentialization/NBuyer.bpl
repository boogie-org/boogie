// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "pid"} Pid = int;
const n:int;      // Number of buyers
const price:int;  // Item price
const wallet:int; // Available money for each buyer

axiom n > 1 && wallet >= 0 && price >= 0;

// Contribution of each node (initially 0)
var {:layer 0,6} contribution:[int]int;
// Channel of the seller for request messages from the first buyer
var {:layer 0,6} RequestChannel:int;
// Channel of the buyers for quote messages from the seller
var {:layer 0,6} QuoteChannel:[int][int]int;
// Channel of the buyers for remaining amount messages from other buyers
var {:layer 0,6} RemainderChannel:[int][int]int;
// Channel of the seller for receiving final decision message from the last buyer
var {:layer 0,6} DecisionChannel:[bool]int;

function {:inline} sellerID (pid:int) : bool { pid == 0 }
function {:inline} buyerID (pid:int) : bool { 1 <= pid && pid <= n }
function {:inline} firstBuyerID (pid:int) : bool { pid == 1 }
function {:inline} middleBuyerID (pid:int) : bool { 1 < pid && pid < n }
function {:inline} lastBuyerID (pid:int) : bool { pid == n }
function {:inline} nextBuyer(pid:int) : int { pid + 1 }

function {:inline} min (x:int, y:int) : int {if x < y then x else y}

function sum(A:[int]int, i:int, j:int) : int
{
  if j < i then 0 else
  if i == j then A[i] else
  sum(A, i, j-1) + A[j]
}

axiom (forall A:[int]int, k:int, k':int, v:int :: k' > k && k > 0 ==> sum(A[k' := v], 1, k) == sum(A, 1, k));
axiom (forall A:[int]int, B:[int]int, i:int, j:int :: i <= j && (forall l:int :: i <= l && l <= j ==> A[l] == B[l]) ==> sum(A, i, j) == sum(B, i, j));

////////////////////////////////////////////////////////////////////////////////

function {:inline} Init(pids:[int]bool, RequestChannel:int, QuoteChannel:[int][int]int,
  RemainderChannel:[int][int]int, DecisionChannel:[bool]int, contribution:[int]int) : bool
{
  pids == MapConst(true) &&
  RequestChannel == 0 &&
  QuoteChannel == (lambda i:int :: MapConst(0)) &&
  RemainderChannel == (lambda i:int :: MapConst(0)) &&
  DecisionChannel == MapConst(0) &&
  contribution == MapConst(0)
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 6}
MAIN5 ({:linear_in "pid"} pids:[int]bool)
modifies contribution;
{
  assert Init(pids, RequestChannel, QuoteChannel, RemainderChannel, DecisionChannel, contribution);
  havoc contribution;
}

procedure {:layer 5}
{:creates "SellerFinish"}
{:IS_invariant}{:elim "SellerFinish","SellerFinish'"}
INV4 ({:linear_in "pid"} pids:[int]bool)
modifies DecisionChannel, contribution;
{
  assert Init(pids, RequestChannel, QuoteChannel, RemainderChannel, DecisionChannel, contribution);
  havoc contribution;
  if (*)
  {
    DecisionChannel := MapConst(0)[(sum(contribution, 1, n) == price) := 1];
    call create_async(SellerFinish(0));
  }
}

procedure {:IS_abstraction}{:layer 5}
SellerFinish' ({:linear_in "pid"} pid:int)
modifies DecisionChannel;
{
  var dec:bool;
  assert sellerID(pid);
  dec := (sum(contribution, 1, n) == price);
  assert DecisionChannel == MapConst(0)[dec := 1];
  DecisionChannel[dec] := DecisionChannel[dec] - 1;
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 5}
{:creates "SellerFinish"}
{:IS "MAIN5","INV4"}
MAIN4 ({:linear_in "pid"} pids:[int]bool)
modifies DecisionChannel, contribution;
{
  assert Init(pids, RequestChannel, QuoteChannel, RemainderChannel, DecisionChannel, contribution);
  havoc contribution;
  DecisionChannel := MapConst(0)[(sum(contribution, 1, n) == price) := 1];
  call create_async(SellerFinish(0));
}

procedure {:layer 4}
{:creates "SellerFinish","FirstBuyer","MiddleBuyer","LastBuyer"}
{:IS_invariant}{:elim "FirstBuyer","FirstBuyer'"}{:elim "MiddleBuyer","MiddleBuyer'"}{:elim "LastBuyer","LastBuyer'"}
INV3 ({:linear_in "pid"} pids:[int]bool)
modifies QuoteChannel, RemainderChannel, DecisionChannel, contribution;
{
  var {:pool "INV3"} k: int;
  var {:pool "contribution"} c: [int]int;

  assert Init(pids, RequestChannel, QuoteChannel, RemainderChannel, DecisionChannel, contribution);

  contribution := c;
  assume {:add_to_pool "INV3", 0, 1, k, k+1, n} true;
  call create_async(SellerFinish(0));
  if (*)
  {
    QuoteChannel := (lambda i:int :: if buyerID(i) then MapConst(0)[price := 1] else MapConst(0));
    call create_async(LastBuyer(n));
    call create_async(FirstBuyer(1));
    call create_asyncs((lambda pa:MiddleBuyer :: middleBuyerID(pa->pid)));
    call set_choice(FirstBuyer(1));
  }
  else if (*)
  {
    assume 1 <= k && k < n && 0 <= sum(contribution, 1, k) && sum(contribution, 1, k) <= price;
    QuoteChannel := (lambda i:int :: if buyerID(i) && i > k then MapConst(0)[price := 1] else MapConst(0));
    RemainderChannel := (lambda i:int :: if i == k+1 then MapConst(0)[(price - sum(contribution, 1, k)) := 1] else MapConst(0));
    call create_async(LastBuyer(n));
    call create_asyncs((lambda pa:MiddleBuyer :: middleBuyerID(pa->pid) && pa->pid > k));
    if (lastBuyerID(k+1))
    {
      call set_choice(LastBuyer(k+1));
    }
    else
    {
      call set_choice(MiddleBuyer(k+1));
    }
  }
  else if (*)
  {
    QuoteChannel := (lambda i:int :: if lastBuyerID(i) then MapConst(0)[price := 1] else MapConst(0));
    assume 0 <= sum(contribution, 1, n-1) && sum(contribution, 1, n-1) <= price;
    RemainderChannel := (lambda i:int :: if i == n then MapConst(0)[(price - sum(contribution, 1, n-1)) := 1] else MapConst(0));
    call create_async(LastBuyer(n));
    call set_choice(LastBuyer(n));
  }
  else
  {
    DecisionChannel := MapConst(0)[(sum(contribution, 1, n) == price) := 1];
  }
}

procedure {:IS_abstraction}{:layer 4}
FirstBuyer' ({:linear_in "pid"} pid:int)
modifies QuoteChannel, RemainderChannel, contribution;
{
  assert DecisionChannel == MapConst(0);
  assert (forall i:int :: i != pid ==> RemainderChannel[i] == MapConst(0));
  assert QuoteChannel[pid][price] > 0;
  call FirstBuyer(pid);
}

procedure {:IS_abstraction}{:layer 4}
MiddleBuyer' ({:linear_in "pid"} pid:int)
modifies QuoteChannel, RemainderChannel, contribution;
{
  assert (forall r:int :: RemainderChannel[pid][r] > 0 ==> r == price - sum(contribution, 1, pid - 1));
  assert RemainderChannel[pid][price - sum(contribution, 1, pid - 1)] > 0;
  assert DecisionChannel == MapConst(0);
  assert (forall i:int :: i < pid ==> QuoteChannel[i] == MapConst(0));
  assert (forall i:int :: i != pid ==> RemainderChannel[i] == MapConst(0));
  assert QuoteChannel[pid][price] > 0;
  call MiddleBuyer(pid);
}

procedure {:IS_abstraction}{:layer 4}
LastBuyer' ({:linear_in "pid"} pid:int)
modifies QuoteChannel, RemainderChannel, DecisionChannel, contribution;
{
  assert (forall r:int :: RemainderChannel[pid][r] > 0 ==> r == price - sum(contribution, 1, pid - 1));
  assert RemainderChannel[n][price - sum(contribution, 1, n-1)] > 0;
  assert DecisionChannel == MapConst(0);
  assert (forall i:int :: i < pid ==> QuoteChannel[i] == MapConst(0));
  assert QuoteChannel[pid][price] > 0;
  call LastBuyer(pid);
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 4}
{:creates "SellerFinish","FirstBuyer","MiddleBuyer","LastBuyer"}
{:IS "MAIN4","INV3"}
MAIN3 ({:linear_in "pid"} pids:[int]bool)
modifies QuoteChannel;
{
  assert Init(pids, RequestChannel, QuoteChannel, RemainderChannel, DecisionChannel, contribution);

  assume {:add_to_pool "contribution", contribution} true;
  QuoteChannel := (lambda i:int :: if buyerID(i) then MapConst(0)[price := 1] else MapConst(0));
  call create_async(SellerFinish(0));
  call create_async(FirstBuyer(1));
  call create_async(LastBuyer(n));
  call create_asyncs((lambda pa:MiddleBuyer :: middleBuyerID(pa->pid)));
}

procedure {:layer 3}
{:creates "SellerInit","SellerFinish","FirstBuyer","MiddleBuyer","LastBuyer"}
{:IS_invariant}{:elim "SellerInit","SellerInit'"}
INV2 ({:linear_in "pid"} pids:[int]bool)
modifies RequestChannel, QuoteChannel;
{
  assert Init(pids, RequestChannel, QuoteChannel, RemainderChannel, DecisionChannel, contribution);
  if (*)
  {
    RequestChannel := 1;
    call create_async(SellerInit(0));
  }
  else
  {
    QuoteChannel := (lambda i:int :: if buyerID(i) then MapConst(0)[price := 1] else MapConst(0));
    call create_async(SellerFinish(0));
  }
  call create_async(FirstBuyer(1));
  call create_async(LastBuyer(n));
  call create_asyncs((lambda pa:MiddleBuyer :: middleBuyerID(pa->pid)));
}

procedure {:IS_abstraction}{:layer 3}
{:creates "SellerFinish"}
SellerInit' ({:linear_in "pid"} pid:int)
modifies RequestChannel, QuoteChannel;
{
  assert QuoteChannel == (lambda i:int :: MapConst(0)); // To discharge gate failure preservation for FirstBuyer/MiddleBuyer/LastBuyer
  assert RequestChannel > 0;
  call SellerInit(pid);
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 3}
{:creates "SellerInit","FirstBuyer","MiddleBuyer","LastBuyer"}
{:IS "MAIN3","INV2"}
MAIN2 ({:linear_in "pid"} pids:[int]bool)
modifies RequestChannel;
{
  assert Init(pids, RequestChannel, QuoteChannel, RemainderChannel, DecisionChannel, contribution);
  RequestChannel := 1;
  call create_async(SellerInit(0));
  call create_async(FirstBuyer(1));
  call create_async(LastBuyer(n));
  call create_asyncs((lambda pa:MiddleBuyer :: middleBuyerID(pa->pid)));
}

procedure {:layer 2}
{:creates "SellerInit","FirstBuyerInit","FirstBuyer","MiddleBuyer","LastBuyer"}
{:IS_invariant}{:elim "FirstBuyerInit"}
INV1 ({:linear_in "pid"} pids:[int]bool)
modifies RequestChannel;
{
  assert Init(pids, RequestChannel, QuoteChannel, RemainderChannel, DecisionChannel, contribution);
  if (*)
  {
    call create_async(FirstBuyerInit(1));
  }
  else
  {
    RequestChannel := 1;
    call create_async(FirstBuyer(1));
  }
  call create_async(SellerInit(0));
  call create_async(LastBuyer(n));
  call create_asyncs((lambda pa:MiddleBuyer :: middleBuyerID(pa->pid)));
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}
{:creates "SellerInit","FirstBuyerInit","MiddleBuyer","LastBuyer"}
{:IS "MAIN2","INV1"}
MAIN1 ({:linear_in "pid"} pids:[int]bool)
{
  assert Init(pids, RequestChannel, QuoteChannel, RemainderChannel, DecisionChannel, contribution);
  call create_async(SellerInit(0));
  call create_async(FirstBuyerInit(1));
  call create_async(LastBuyer(n));
  call create_asyncs((lambda pa:MiddleBuyer :: middleBuyerID(pa->pid)));
}

procedure {:atomic}{:layer 2,3}
{:pending_async}
{:creates "SellerFinish"}
SellerInit ({:linear_in "pid"} pid:int)
modifies RequestChannel, QuoteChannel;
{
  assert sellerID(pid);

  assume RequestChannel > 0;
  RequestChannel := RequestChannel - 1;

  QuoteChannel := (lambda i:int :: (lambda q:int :: if buyerID(i) && q == price then QuoteChannel[i][q] + 1 else QuoteChannel[i][q]));
  call create_async(SellerFinish(pid));
}

procedure {:atomic}{:layer 2,5}
{:pending_async}
SellerFinish ({:linear_in "pid"} pid:int)
modifies DecisionChannel;
{
  var dec:bool;
  assert sellerID(pid);
  assert DecisionChannel[true] > 0 ==> sum(contribution, 1, n) == price;

  assume DecisionChannel[dec] > 0;
  DecisionChannel[dec] := DecisionChannel[dec] - 1;
}

procedure {:atomic}{:layer 2,4}
{:pending_async}
{:creates "FirstBuyer"}
FirstBuyerInit ({:linear_in "pid"} pid:int)
modifies RequestChannel;
{
  assert firstBuyerID(pid);
  RequestChannel := RequestChannel + 1;
  call create_async(FirstBuyer(pid));
}

procedure {:atomic}{:layer 2,4}
{:pending_async}
FirstBuyer ({:linear_in "pid"} pid:int)
modifies QuoteChannel, RemainderChannel, contribution;
{
  var rem:int;
  var amount:int;

  assert firstBuyerID(pid);
  assert (forall q:int :: QuoteChannel[pid][q] > 0 ==> q == price);

  assume QuoteChannel[pid][price] > 0;
  QuoteChannel[pid][price] := QuoteChannel[pid][price] - 1;

  rem := price;
  if (*) { amount := min(wallet, rem); } else { amount := 0; }
  contribution[pid] := amount;
  assume {:add_to_pool "contribution", contribution} true;
  rem := rem - amount;
  RemainderChannel[nextBuyer(pid)][rem] := RemainderChannel[nextBuyer(pid)][rem] + 1;
}

procedure {:atomic}{:layer 2,4}
{:pending_async}
MiddleBuyer ({:linear_in "pid"} pid:int)
modifies QuoteChannel, RemainderChannel, contribution;
{
  var rem:int;
  var amount:int;

  assert middleBuyerID(pid);
  assert (forall q:int :: QuoteChannel[pid][q] > 0 ==> q == price);
  assert (forall r:int :: RemainderChannel[pid][r] > 0 ==> 0 <= r && r <= price);

  assume QuoteChannel[pid][price] > 0;
  QuoteChannel[pid][price] := QuoteChannel[pid][price] - 1;

  assume RemainderChannel[pid][rem] > 0;
  RemainderChannel[pid][rem] := RemainderChannel[pid][rem] - 1;

  if (*) { amount := min(wallet, rem); } else { amount := 0; }
  contribution[pid] := amount;
  assume {:add_to_pool "contribution", contribution} true;
  rem := rem - amount;
  RemainderChannel[nextBuyer(pid)][rem] := RemainderChannel[nextBuyer(pid)][rem] + 1;
}

procedure {:atomic}{:layer 2,4}
{:pending_async}
LastBuyer ({:linear_in "pid"} pid:int)
modifies QuoteChannel, RemainderChannel, DecisionChannel, contribution;
{
  var rem:int;
  var amount:int;

  assert lastBuyerID(pid);
  assert (forall q:int :: QuoteChannel[pid][q] > 0 ==> q == price);
  assert (forall r:int :: RemainderChannel[pid][r] > 0 ==> 0 <= r && r <= price);

  assume QuoteChannel[pid][price] > 0;
  QuoteChannel[pid][price] := QuoteChannel[pid][price] - 1;

  assume RemainderChannel[pid][rem] > 0;
  RemainderChannel[pid][rem] := RemainderChannel[pid][rem] - 1;

  if (*) { amount := min(wallet, rem); } else { amount := 0; }
  contribution[pid] := amount;
  assume {:add_to_pool "contribution", contribution} true;
  if (amount == rem)
  {
      DecisionChannel[true] := DecisionChannel[true] + 1;
  }
  else
  {
    DecisionChannel[false] := DecisionChannel[false] + 1;
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:yields}{:layer 1}{:refines "MAIN1"}
main ({:linear_in "pid"} pids:[int]bool)
requires {:layer 1} Init(pids, RequestChannel, QuoteChannel, RemainderChannel, DecisionChannel, contribution);
{
  var i:int;
  var {:pending_async}{:layer 1} SellerInit_PAs:[SellerInit]int;
  var {:pending_async}{:layer 1} FirstBuyerInit_PAs:[FirstBuyerInit]int;
  var {:pending_async}{:layer 1} LastBuyer_PAs:[LastBuyer]int;
  var {:pending_async}{:layer 1} MiddleBuyer_PAs:[MiddleBuyer]int;
  var {:linear "pid"} pid:int;
  var {:linear "pid"} pids':[int]bool;

  pids' := pids;
  call pid, pids' := linear_transfer(0, pids');
  async call sellerInit(pid);
  call pid, pids' := linear_transfer(1, pids');
  async call firstBuyerInit(pid);
  call pid, pids' := linear_transfer(n, pids');
  async call lastBuyer(pid);
  i := 2;
  while (i < n)
  invariant {:layer 1} 2 <= i && i <= n;
  invariant {:layer 1} (forall ii:int :: middleBuyerID(ii) && ii >= i ==> pids'[ii]);
  invariant {:layer 1} MiddleBuyer_PAs == (lambda pa:MiddleBuyer :: if middleBuyerID(pa->pid) && pa->pid < i then 1 else 0);
  {
    call pid, pids' := linear_transfer(i, pids');
    async call middleBuyer(pid);
    i := i + 1;
  }
}

procedure {:yields}{:layer 1}{:refines "SellerInit"}
sellerInit ({:linear_in "pid"} pid:int)
requires {:layer 1} sellerID(pid);
{
  var i:int;
  var {:layer 1} old_QuoteChannel:[int][int]int;

  call old_QuoteChannel := Snapshot_QuoteChannel();
  call receive_request();
  i := 1;
  while (i <= n)
  invariant {:layer 1} 1 <= i && i <= n+1;
  invariant {:layer 1} QuoteChannel == (lambda ii:int :: (lambda q:int :: if buyerID(ii) && ii < i && q == price then old_QuoteChannel[ii][q] + 1 else old_QuoteChannel[ii][q]));
  {
    call send_quote(i, price);
    i := i + 1;
  }
  async call sellerFinish(pid);
}

procedure {:yields}{:layer 1}{:refines "SellerFinish"}
sellerFinish ({:linear_in "pid"} pid:int)
requires {:layer 1} sellerID(pid);
{
  var d:bool;

  call d := receive_decision();
  if (d)
  {
    call assert_sum();
  }
}

procedure {:yields}{:layer 1}{:refines "FirstBuyerInit"}
firstBuyerInit ({:linear_in "pid"} pid:int)
requires {:layer 1} firstBuyerID(pid);
{
  call send_request();
  async call firstBuyer(pid);
}


procedure {:yields}{:layer 1}{:refines "FirstBuyer"}
firstBuyer ({:linear_in "pid"} pid:int)
requires {:layer 1} firstBuyerID(pid);
{
  var q:int;
  var amount:int;

  call q := receive_quote(pid);
  if (*) { amount := min(wallet, q); } else { amount := 0; }
  call set_contribution(pid, amount);
  call send_remainder(nextBuyer(pid), q - amount);
}

procedure {:yields}{:layer 1}{:refines "MiddleBuyer"}
middleBuyer ({:linear_in "pid"} pid:int)
requires {:layer 1} middleBuyerID(pid);
{
  var q:int;
  var r:int;
  var amount:int;

  call q := receive_quote(pid);
  call r := receive_remainder(pid);
  if (*) { amount := min(wallet, r); } else { amount := 0; }
  call set_contribution(pid, amount);
  call send_remainder(nextBuyer(pid), r - amount);
}

procedure {:yields}{:layer 1}{:refines "LastBuyer"}
lastBuyer ({:linear_in "pid"} pid:int)
requires {:layer 1} lastBuyerID(pid);
{
  var q:int;
  var r:int;
  var amount:int;

  call q := receive_quote(pid);
  call r := receive_remainder(pid);
  if (*) { amount := min(wallet, r); } else { amount := 0; }
  call set_contribution(pid, amount);
  call send_decision(amount == r);
}

procedure {:intro}{:layer 1} Snapshot_QuoteChannel() returns (snapshot:[int][int]int)
{
  snapshot := QuoteChannel;
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 1} SET_CONTRIBUTION({:linear "pid"} pid:int, c:int)
modifies contribution;
{
  contribution[pid] := c;
}

procedure {:atomic}{:layer 1} ASSERT_SUM()
{
  assert sum(contribution, 1, n) == price;
}

procedure {:left}{:layer 1} SEND_REQUEST()
modifies RequestChannel;
{
  RequestChannel := RequestChannel + 1;
}

procedure {:right}{:layer 1} RECEIVE_REQUEST()
modifies RequestChannel;
{
  assume RequestChannel > 0;
  RequestChannel := RequestChannel - 1;
}

procedure {:left}{:layer 1} SEND_QUOTE(pid:int, q:int)
modifies QuoteChannel;
{
  QuoteChannel[pid][q] := QuoteChannel[pid][q] + 1;
}

procedure {:right}{:layer 1} RECEIVE_QUOTE(pid:int) returns (q:int)
modifies QuoteChannel;
{
  assume QuoteChannel[pid][q] > 0;
  QuoteChannel[pid][q] := QuoteChannel[pid][q] - 1;
}

procedure {:left}{:layer 1} SEND_REMAINDER(pid:int, r:int)
modifies RemainderChannel;
{
  RemainderChannel[pid][r] := RemainderChannel[pid][r] + 1;
}

procedure {:right}{:layer 1} RECEIVE_REMAINDER(pid:int) returns (r:int)
modifies RemainderChannel;
{
  assume RemainderChannel[pid][r] > 0;
  RemainderChannel[pid][r] := RemainderChannel[pid][r] - 1;
}

procedure {:left}{:layer 1} SEND_DECISION(d:bool)
modifies DecisionChannel;
{
  DecisionChannel[d] := DecisionChannel[d] + 1;
}

procedure {:right}{:layer 1} RECEIVE_DECISION() returns (d:bool)
modifies DecisionChannel;
{
  assume DecisionChannel[d] > 0;
  DecisionChannel[d] := DecisionChannel[d] - 1;
}

procedure {:yields}{:layer 0}{:refines "SET_CONTRIBUTION"} set_contribution({:linear "pid"} pid:int, c:int);
procedure {:yields}{:layer 0}{:refines "ASSERT_SUM"} assert_sum();
procedure {:yields}{:layer 0}{:refines "SEND_REQUEST"} send_request();
procedure {:yields}{:layer 0}{:refines "RECEIVE_REQUEST"} receive_request();
procedure {:yields}{:layer 0}{:refines "SEND_QUOTE"} send_quote(pid:int, q:int);
procedure {:yields}{:layer 0}{:refines "RECEIVE_QUOTE"} receive_quote(pid:int) returns (q:int);
procedure {:yields}{:layer 0}{:refines "SEND_REMAINDER"} send_remainder(pid:int, r:int);
procedure {:yields}{:layer 0}{:refines "RECEIVE_REMAINDER"} receive_remainder(pid:int) returns (r:int);
procedure {:yields}{:layer 0}{:refines "SEND_DECISION"} send_decision(d:bool);
procedure {:yields}{:layer 0}{:refines "RECEIVE_DECISION"} receive_decision() returns (d:bool);

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
