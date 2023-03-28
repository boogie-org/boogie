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
var {:layer 0,1} RequestChannel:int;
// Channel of the buyers for quote messages from the seller
var {:layer 0,1} QuoteChannel:[int][int]int;
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

function {:inline} Init(pids:[int]bool, RemainderChannel:[int][int]int, DecisionChannel:[bool]int, contribution:[int]int) : bool
{
  pids == MapConst(true) &&
  RemainderChannel == (lambda i:int :: MapConst(0)) &&
  DecisionChannel == MapConst(0) &&
  contribution == MapConst(0)
}

////////////////////////////////////////////////////////////////////////////////

action {:layer 6}
MAIN5 ({:linear_in "pid"} pids:[int]bool)
modifies contribution;
{
  assert Init(pids, RemainderChannel, DecisionChannel, contribution);
  havoc contribution;
}

invariant action {:layer 5}{:elim "SellerFinish","SellerFinish'"}
INV4 ({:linear_in "pid"} pids:[int]bool)
creates SellerFinish;
modifies DecisionChannel, contribution;
{
  assert Init(pids, RemainderChannel, DecisionChannel, contribution);
  havoc contribution;
  if (*)
  {
    DecisionChannel := MapConst(0)[(sum(contribution, 1, n) == price) := 1];
    call create_async(SellerFinish(0));
  }
}

abstract action {:layer 5} SellerFinish' ({:linear_in "pid"} pid:int)
modifies DecisionChannel;
{
  assert DecisionChannel == MapConst(0)[(sum(contribution, 1, n) == price) := 1];
  call SellerFinish(pid);
}

////////////////////////////////////////////////////////////////////////////////

action {:layer 5} MAIN4 ({:linear_in "pid"} pids:[int]bool) refines MAIN5 using INV4
creates SellerFinish;
modifies DecisionChannel, contribution;
{
  assert Init(pids, RemainderChannel, DecisionChannel, contribution);
  havoc contribution;
  DecisionChannel := MapConst(0)[(sum(contribution, 1, n) == price) := 1];
  call create_async(SellerFinish(0));
}

invariant action {:layer 4}{:elim "FirstBuyer","FirstBuyer'"}{:elim "MiddleBuyer","MiddleBuyer'"}{:elim "LastBuyer","LastBuyer'"}
INV3 ({:linear_in "pid"} pids:[int]bool)
creates SellerFinish, FirstBuyer, MiddleBuyer, LastBuyer;
modifies RemainderChannel, DecisionChannel, contribution;
{
  var {:pool "INV3"} k: int;
  var {:pool "contribution"} c: [int]int;

  assert Init(pids, RemainderChannel, DecisionChannel, contribution);

  contribution := c;
  assume {:add_to_pool "INV3", 0, 1, k, k+1, n} true;
  call create_async(SellerFinish(0));
  if (*)
  {
    call create_async(LastBuyer(n));
    call create_async(FirstBuyer(1));
    call create_asyncs((lambda pa:MiddleBuyer :: middleBuyerID(pa->pid)));
    call set_choice(FirstBuyer(1));
  }
  else if (*)
  {
    assume 1 <= k && k < n && 0 <= sum(contribution, 1, k) && sum(contribution, 1, k) <= price;
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

abstract action {:layer 4} FirstBuyer' ({:linear_in "pid"} pid:int)
modifies RemainderChannel, contribution;
{
  assert DecisionChannel == MapConst(0);
  assert (forall i:int :: i != pid ==> RemainderChannel[i] == MapConst(0));
  call FirstBuyer(pid);
}

abstract action {:layer 4} MiddleBuyer' ({:linear_in "pid"} pid:int)
modifies RemainderChannel, contribution;
{
  assert (forall r:int :: RemainderChannel[pid][r] > 0 ==> r == price - sum(contribution, 1, pid - 1));
  assert RemainderChannel[pid][price - sum(contribution, 1, pid - 1)] > 0;
  assert DecisionChannel == MapConst(0);
  assert (forall i:int :: i != pid ==> RemainderChannel[i] == MapConst(0));
  call MiddleBuyer(pid);
}

abstract action {:layer 4} LastBuyer' ({:linear_in "pid"} pid:int)
modifies RemainderChannel, DecisionChannel, contribution;
{
  assert (forall r:int :: RemainderChannel[pid][r] > 0 ==> r == price - sum(contribution, 1, pid - 1));
  assert RemainderChannel[n][price - sum(contribution, 1, n-1)] > 0;
  assert DecisionChannel == MapConst(0);
  call LastBuyer(pid);
}

////////////////////////////////////////////////////////////////////////////////

action {:layer 4} MAIN3 ({:linear_in "pid"} pids:[int]bool) refines MAIN4 using INV3
creates SellerFinish, FirstBuyer, MiddleBuyer, LastBuyer;
{
  assert Init(pids, RemainderChannel, DecisionChannel, contribution);

  assume {:add_to_pool "contribution", contribution} true;
  call create_async(SellerFinish(0));
  call create_async(FirstBuyer(1));
  call create_async(LastBuyer(n));
  call create_asyncs((lambda pa:MiddleBuyer :: middleBuyerID(pa->pid)));
}

invariant action {:layer 3}{:elim "SellerInit"} INV2 ({:linear_in "pid"} pids:[int]bool)
creates SellerInit, SellerFinish, FirstBuyer, MiddleBuyer, LastBuyer;
{
  assert Init(pids, RemainderChannel, DecisionChannel, contribution);
  if (*)
  {
    call create_async(SellerInit(0));
  }
  else
  {
    call create_async(SellerFinish(0));
  }
  call create_async(FirstBuyer(1));
  call create_async(LastBuyer(n));
  call create_asyncs((lambda pa:MiddleBuyer :: middleBuyerID(pa->pid)));
}

////////////////////////////////////////////////////////////////////////////////

action {:layer 3} MAIN2 ({:linear_in "pid"} pids:[int]bool) refines MAIN3 using INV2
creates SellerInit, FirstBuyer, MiddleBuyer, LastBuyer;
{
  assert Init(pids, RemainderChannel, DecisionChannel, contribution);
  call create_async(SellerInit(0));
  call create_async(FirstBuyer(1));
  call create_async(LastBuyer(n));
  call create_asyncs((lambda pa:MiddleBuyer :: middleBuyerID(pa->pid)));
}

invariant action {:layer 2}{:elim "FirstBuyerInit"}
INV1 ({:linear_in "pid"} pids:[int]bool)
creates SellerInit, FirstBuyerInit, FirstBuyer, MiddleBuyer, LastBuyer;
{
  assert Init(pids, RemainderChannel, DecisionChannel, contribution);
  if (*)
  {
    call create_async(FirstBuyerInit(1));
  }
  else
  {
    call create_async(FirstBuyer(1));
  }
  call create_async(SellerInit(0));
  call create_async(LastBuyer(n));
  call create_asyncs((lambda pa:MiddleBuyer :: middleBuyerID(pa->pid)));
}

////////////////////////////////////////////////////////////////////////////////

action {:layer 2} MAIN1 ({:linear_in "pid"} pids:[int]bool) refines MAIN2 using INV1
creates SellerInit, FirstBuyerInit, MiddleBuyer, LastBuyer;
{
  assert Init(pids, RemainderChannel, DecisionChannel, contribution);
  call create_async(SellerInit(0));
  call create_async(FirstBuyerInit(1));
  call create_async(LastBuyer(n));
  call create_asyncs((lambda pa:MiddleBuyer :: middleBuyerID(pa->pid)));
}

async action {:layer 2,3} SellerInit ({:linear_in "pid"} pid:int)
creates SellerFinish;
{
  assert sellerID(pid);
  call create_async(SellerFinish(pid));
}

async action {:layer 2,5} SellerFinish ({:linear_in "pid"} pid:int)
modifies DecisionChannel;
{
  var dec:bool;
  assert sellerID(pid);
  assert DecisionChannel[true] > 0 ==> sum(contribution, 1, n) == price;
  assume DecisionChannel[dec] > 0;
  DecisionChannel[dec] := DecisionChannel[dec] - 1;
}

async action {:layer 2,4} FirstBuyerInit ({:linear_in "pid"} pid:int)
creates FirstBuyer;
{
  assert firstBuyerID(pid);
  call create_async(FirstBuyer(pid));
}

async action {:layer 2,4} FirstBuyer ({:linear_in "pid"} pid:int)
modifies RemainderChannel, contribution;
{
  var rem:int;
  var amount:int;

  assert firstBuyerID(pid);
  if (*) { amount := min(wallet, price); } else { amount := 0; }
  contribution[pid] := amount;
  assume {:add_to_pool "contribution", contribution} true;
  rem := price - amount;
  RemainderChannel[nextBuyer(pid)][rem] := RemainderChannel[nextBuyer(pid)][rem] + 1;
}

async action {:layer 2,4} MiddleBuyer ({:linear_in "pid"} pid:int)
modifies RemainderChannel, contribution;
{
  var rem:int;
  var amount:int;

  assert middleBuyerID(pid);
  assert (forall r:int :: RemainderChannel[pid][r] > 0 ==> 0 <= r && r <= price);
  assume RemainderChannel[pid][rem] > 0;
  RemainderChannel[pid][rem] := RemainderChannel[pid][rem] - 1;
  if (*) { amount := min(wallet, rem); } else { amount := 0; }
  contribution[pid] := amount;
  assume {:add_to_pool "contribution", contribution} true;
  rem := rem - amount;
  RemainderChannel[nextBuyer(pid)][rem] := RemainderChannel[nextBuyer(pid)][rem] + 1;
}

async action {:layer 2,4} LastBuyer ({:linear_in "pid"} pid:int)
modifies RemainderChannel, DecisionChannel, contribution;
{
  var rem:int;
  var amount:int;

  assert lastBuyerID(pid);
  assert (forall r:int :: RemainderChannel[pid][r] > 0 ==> 0 <= r && r <= price);
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

yield invariant {:layer 1} YieldInit({:linear "pid"} pids:[int]bool);
invariant Init(pids, RemainderChannel, DecisionChannel, contribution);

yield invariant {:layer 1} YieldInv();
invariant (forall ii: int, q: int :: QuoteChannel[ii][q] > 0 ==> q == price);

yield procedure {:layer 1} main ({:linear_in "pid"} pids:[int]bool) refines MAIN1
requires call YieldInit(pids);
preserves call YieldInv();
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

yield procedure {:layer 1} sellerInit ({:linear_in "pid"} pid:int) refines SellerInit
requires {:layer 1} sellerID(pid);
preserves call YieldInv();
{
  var i:int;

  call receive_request();
  i := 1;
  while (i <= n)
  invariant {:yields} true;
  invariant call YieldInv();
  invariant {:layer 1} 1 <= i && i <= n+1;
  {
    call send_quote(i, price);
    i := i + 1;
  }
  async call sellerFinish(pid);
}

yield procedure {:layer 1} sellerFinish ({:linear_in "pid"} pid:int) refines SellerFinish
requires {:layer 1} sellerID(pid);
preserves call YieldInv();
{
  var d:bool;

  call d := receive_decision();
  if (d)
  {
    call assert_sum();
  }
}

yield procedure {:layer 1} firstBuyerInit ({:linear_in "pid"} pid:int) refines FirstBuyerInit
requires {:layer 1} firstBuyerID(pid);
preserves call YieldInv();
{
  call send_request();
  async call firstBuyer(pid);
}


yield procedure {:layer 1} firstBuyer ({:linear_in "pid"} pid:int) refines FirstBuyer
requires {:layer 1} firstBuyerID(pid);
preserves call YieldInv();
{
  var q:int;
  var amount:int;

  call q := receive_quote(pid);
  if (*) { amount := min(wallet, q); } else { amount := 0; }
  call set_contribution(pid, amount);
  call send_remainder(nextBuyer(pid), q - amount);
}

yield procedure {:layer 1} middleBuyer ({:linear_in "pid"} pid:int) refines MiddleBuyer
requires {:layer 1} middleBuyerID(pid);
preserves call YieldInv();
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

yield procedure {:layer 1} lastBuyer ({:linear_in "pid"} pid:int) refines LastBuyer
requires {:layer 1} lastBuyerID(pid);
preserves call YieldInv();
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

////////////////////////////////////////////////////////////////////////////////

action {:layer 1} SET_CONTRIBUTION({:linear "pid"} pid:int, c:int)
modifies contribution;
{
  contribution[pid] := c;
}

action {:layer 1} ASSERT_SUM()
{
  assert sum(contribution, 1, n) == price;
}

<- action {:layer 1} SEND_REQUEST()
modifies RequestChannel;
{
  RequestChannel := RequestChannel + 1;
}

-> action {:layer 1} RECEIVE_REQUEST()
modifies RequestChannel;
{
  assume RequestChannel > 0;
  RequestChannel := RequestChannel - 1;
}

<- action {:layer 1} SEND_QUOTE(pid:int, q:int)
modifies QuoteChannel;
{
  QuoteChannel[pid][q] := QuoteChannel[pid][q] + 1;
}

-> action {:layer 1} RECEIVE_QUOTE(pid:int) returns (q:int)
modifies QuoteChannel;
{
  assume QuoteChannel[pid][q] > 0;
  QuoteChannel[pid][q] := QuoteChannel[pid][q] - 1;
}

<- action {:layer 1} SEND_REMAINDER(pid:int, r:int)
modifies RemainderChannel;
{
  RemainderChannel[pid][r] := RemainderChannel[pid][r] + 1;
}

-> action {:layer 1} RECEIVE_REMAINDER(pid:int) returns (r:int)
modifies RemainderChannel;
{
  assume RemainderChannel[pid][r] > 0;
  RemainderChannel[pid][r] := RemainderChannel[pid][r] - 1;
}

<- action {:layer 1} SEND_DECISION(d:bool)
modifies DecisionChannel;
{
  DecisionChannel[d] := DecisionChannel[d] + 1;
}

-> action {:layer 1} RECEIVE_DECISION() returns (d:bool)
modifies DecisionChannel;
{
  assume DecisionChannel[d] > 0;
  DecisionChannel[d] := DecisionChannel[d] - 1;
}

yield procedure {:layer 0} set_contribution({:linear "pid"} pid:int, c:int) refines SET_CONTRIBUTION;
yield procedure {:layer 0} assert_sum() refines ASSERT_SUM;
yield procedure {:layer 0} send_request() refines SEND_REQUEST;
yield procedure {:layer 0} receive_request() refines RECEIVE_REQUEST;
yield procedure {:layer 0} send_quote(pid:int, q:int) refines SEND_QUOTE;
yield procedure {:layer 0} receive_quote(pid:int) returns (q:int) refines RECEIVE_QUOTE;
yield procedure {:layer 0} send_remainder(pid:int, r:int) refines SEND_REMAINDER;
yield procedure {:layer 0} receive_remainder(pid:int) returns (r:int) refines RECEIVE_REMAINDER;
yield procedure {:layer 0} send_decision(d:bool) refines SEND_DECISION;
yield procedure {:layer 0} receive_decision() returns (d:bool) refines RECEIVE_DECISION;

<-> action {:layer 1}
LINEAR_TRANSFER(i:int, {:linear_in "pid"} pids:[int]bool)
returns ({:linear "pid"} p:int, {:linear "pid"} pids':[int]bool)
{
  assert pids[i];
  p := i;
  pids' := pids[i := false];
}

yield procedure {:layer 0} linear_transfer(i:int, {:linear_in "pid"} pids:[int]bool)
returns ({:linear "pid"} p:int, {:linear "pid"} pids':[int]bool) refines LINEAR_TRANSFER;
