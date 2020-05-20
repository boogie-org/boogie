// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const n:int;      // Number of buyers
const price:int;  // Item price
const wallet:int; // Available money for each buyer

axiom n > 1 && wallet >= 0 && price >= 0;

var {:layer 0,6} contribution:[int]int; // Contribution of each node (initially 0)

var {:layer 0,6} ReqCH:int;             // Channel of the seller for request messages from the first buyer
var {:layer 0,6} QuoteCH:[int][int]int; // Channel of the buyers for quote messages from the seller
var {:layer 0,6} RemCH:[int][int]int;   // Channel of the buyers for remaining amount messages from other buyers
var {:layer 0,6} DecCH:[bool]int;       // Channel of the seller for receiving final decision message from the last buyer

function {:inline} sellerID (pid:int) : bool { pid == 0 }
function {:inline} buyerID (pid:int) : bool { 1 <= pid && pid <= n }
function {:inline} firstBuyerID (pid:int) : bool { pid == 1 }
function {:inline} middleBuyerID (pid:int) : bool { 1 < pid && pid < n }
function {:inline} lastBuyerID (pid:int) : bool { pid == n }
function {:inline} nextBuyer(pid:int) : int { pid + 1 }

function {:inline} min (x:int, y:int) : int {if x < y then x else y}

type {:pending_async}{:datatype} PA;
function {:pending_async "FirstBuyerInit"}{:constructor} FirstBuyerInitPA(pid:int) : PA;
function {:pending_async "FirstBuyer"}{:constructor} FirstBuyerPA(pid:int) : PA;
function {:pending_async "MiddleBuyer"}{:constructor} MiddleBuyerPA(pid:int) : PA;
function {:pending_async "LastBuyer"}{:constructor} LastBuyerPA(pid:int) : PA;
function {:pending_async "SellerInit"}{:constructor} SellerInitPA(pid:int) : PA;
function {:pending_async "SellerFinish"}{:constructor} SellerFinishPA(pid:int) : PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

function {:inline} SingletonPA (pa:PA) : [PA]int
{ NoPAs()[pa := 1] }

function {:builtin "MapAdd"} MapAddPA([PA]int, [PA]int) : [PA]int;
function MapAddPA3(a:PA, b:PA, c:[PA]int) : [PA]int
{ MapAddPA(SingletonPA(a), MapAddPA(SingletonPA(b), c)) }
function MapAddPA4(a:PA, b:PA, c:PA, d:[PA]int) : [PA]int
{ MapAddPA(SingletonPA(a), MapAddPA(SingletonPA(b), MapAddPA(SingletonPA(c), d))) }

function trigger(x:int) : bool { true }

function sum(A:[int]int, i:int, j:int) : int
{
  if j < i then 0 else
  if i == j then A[i] else
  sum(A, i, j-1) + A[j]
}

axiom (forall A:[int]int, k:int, k':int, v:int :: k' > k && k > 0 ==> sum(A[k' := v], 1, k) == sum(A, 1, k));
axiom (forall A:[int]int, B:[int]int, i:int, j:int :: i <= j && (forall l:int :: i <= l && l <= j ==> A[l] == B[l]) ==> sum(A, i, j) == sum(B, i, j));

////////////////////////////////////////////////////////////////////////////////

function {:inline} Init(pids:[int]bool, ReqCH:int, QuoteCH:[int][int]int,
  RemCH:[int][int]int, DecCH:[bool]int, contribution:[int]int) : bool
{
  pids == MapConstBool(true) &&
  ReqCH == 0 &&
  QuoteCH == (lambda i:int :: (lambda q:int :: 0)) &&
  RemCH == (lambda i:int :: (lambda r:int :: 0)) &&
  DecCH == (lambda b:bool :: 0) &&
  contribution == (lambda i:int :: 0)
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 6}
MAIN5 ({:linear_in "pid"} pids:[int]bool)
modifies contribution;
{
  assert Init(pids, ReqCH, QuoteCH, RemCH, DecCH, contribution);
  havoc contribution;
}

procedure {:IS_invariant}{:layer 5}
INV4 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "SellerFinish"} PAs:[PA]int)
modifies DecCH, contribution;
{
  assert Init(pids, ReqCH, QuoteCH, RemCH, DecCH, contribution);
  havoc contribution;
  if (*)
  {
    DecCH := (lambda b:bool :: if b == (sum(contribution, 1, n) == price) then 1 else 0);
    PAs := SingletonPA(SellerFinishPA(0));
  }
  else
  {
    PAs := NoPAs();
  }
}

procedure {:IS_abstraction}{:layer 5}
SellerFinish' ({:linear_in "pid"} pid:int)
modifies DecCH;
{
  var dec:bool;
  assert sellerID(pid);
  assert DecCH == (lambda b:bool :: if b == (sum(contribution, 1, n) == price) then 1 else 0);
  dec := (sum(contribution, 1, n) == price);
  DecCH[dec] := DecCH[dec] - 1;
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 5}
{:IS "MAIN5","INV4"}{:elim "SellerFinish","SellerFinish'"}
MAIN4 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "SellerFinish"} PAs:[PA]int)
modifies DecCH, contribution;
{
  assert Init(pids, ReqCH, QuoteCH, RemCH, DecCH, contribution);
  havoc contribution;
  DecCH := (lambda b:bool :: if b == (sum(contribution, 1, n) == price) then 1 else 0);
  PAs := SingletonPA(SellerFinishPA(0));
}

procedure {:IS_invariant}{:layer 4}
INV3 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "SellerFinish","FirstBuyer","MiddleBuyer","LastBuyer"} PAs:[PA]int, {:choice} choice:PA)
modifies QuoteCH, RemCH, DecCH, contribution;
{
  assert Init(pids, ReqCH, QuoteCH, RemCH, DecCH, contribution);

  havoc contribution;

  if (*)
  {
    QuoteCH := (lambda i:int :: (lambda q:int :: if buyerID(i) && q == price then 1 else 0));
    PAs := MapAddPA4(SellerFinishPA(0), FirstBuyerPA(1), LastBuyerPA(n), (lambda pa:PA :: if is#MiddleBuyerPA(pa) && middleBuyerID(pid#MiddleBuyerPA(pa)) then 1 else 0));
    choice := FirstBuyerPA(1);
    assume trigger(1);
  }
  else if (*)
  {
    havoc QuoteCH, RemCH;
    assume
    (exists k:int :: {trigger(k)} 1 <= k && k < n && trigger(k+1) &&
      QuoteCH == (lambda i:int :: (lambda q:int :: if buyerID(i) && i > k && q == price then 1 else 0)) &&
      0 <= sum(contribution, 1, k) && sum(contribution, 1, k) <= price &&
      RemCH == (lambda i:int :: (lambda r:int :: if i == k+1 && r == price - sum(contribution, 1, k) then 1 else 0)) &&
      PAs == MapAddPA3(SellerFinishPA(0), LastBuyerPA(n), (lambda pa:PA :: if is#MiddleBuyerPA(pa) && middleBuyerID(pid#MiddleBuyerPA(pa)) && pid#MiddleBuyerPA(pa) > k then 1 else 0)) &&
      (choice == if lastBuyerID(k+1) then LastBuyerPA(k+1) else MiddleBuyerPA(k+1))
    );
  }
  else if (*)
  {
    QuoteCH := (lambda i:int :: (lambda q:int :: if lastBuyerID(i) && q == price then 1 else 0));
    assume 0 <= sum(contribution, 1, n-1) && sum(contribution, 1, n-1) <= price;
    RemCH := (lambda i:int :: (lambda r:int :: if i == n && r == price - sum(contribution, 1, n-1) then 1 else 0));
    PAs := MapAddPA(SingletonPA(SellerFinishPA(0)), SingletonPA(LastBuyerPA(n)));
    choice := LastBuyerPA(n);
  }
  else
  {
    DecCH := (lambda b:bool :: if b == (sum(contribution, 1, n) == price) then 1 else 0);
    PAs := SingletonPA(SellerFinishPA(0));
  }
}

procedure {:IS_abstraction}{:layer 4}
FirstBuyer' ({:linear_in "pid"} pid:int)
modifies QuoteCH, RemCH, contribution;
{
  var rem:int;
  var amount:int;

  assert firstBuyerID(pid);
  assert (forall q:int :: QuoteCH[pid][q] > 0 ==> q == price);

  assert DecCH == (lambda b:bool :: 0);
  assert (forall i:int :: i != pid ==> RemCH[i] == (lambda r:int :: 0));

  assert QuoteCH[pid][price] > 0;
  QuoteCH[pid][price] := QuoteCH[pid][price] - 1;

  rem := price;
  if (*) { amount := min(wallet, rem); } else { amount := 0; }
  contribution[pid] := amount;
  rem := rem - amount;
  RemCH[nextBuyer(pid)][rem] := RemCH[nextBuyer(pid)][rem] + 1;
}

procedure {:IS_abstraction}{:layer 4}
MiddleBuyer' ({:linear_in "pid"} pid:int)
modifies QuoteCH, RemCH, contribution;
{
  var rem:int;
  var amount:int;

  assert middleBuyerID(pid);
  assert (forall q:int :: QuoteCH[pid][q] > 0 ==> q == price);
  assert (forall r:int :: RemCH[pid][r] > 0 ==> 0 <= r && r <= price);
  assert (forall r:int :: RemCH[pid][r] > 0 ==> r == price - sum(contribution, 1, pid - 1));
  assert RemCH[pid][price - sum(contribution, 1, pid - 1)] > 0;
  assert (exists r:int :: RemCH[pid][r] > 0);
  assert DecCH == (lambda b:bool :: 0);
  assert (forall i:int :: i < pid ==> QuoteCH[i] == (lambda r:int :: 0));
  assert (forall i:int :: i != pid ==> RemCH[i] == (lambda r:int :: 0));

  assert QuoteCH[pid][price] > 0;
  assume RemCH[pid][rem] > 0;

  QuoteCH[pid][price] := QuoteCH[pid][price] - 1;
  RemCH[pid][rem] := RemCH[pid][rem] - 1;

  if (*) { amount := min(wallet, rem); } else { amount := 0; }
  contribution[pid] := amount;
  rem := rem - amount;
  RemCH[nextBuyer(pid)][rem] := RemCH[nextBuyer(pid)][rem] + 1;
}

procedure {:IS_abstraction}{:layer 4}
LastBuyer' ({:linear_in "pid"} pid:int)
modifies QuoteCH, RemCH, DecCH, contribution;
{
  var rem:int;
  var amount:int;

  assert lastBuyerID(pid);
  assert (forall q:int :: QuoteCH[pid][q] > 0 ==> q == price);
  assert (forall r:int :: RemCH[pid][r] > 0 ==> 0 <= r && r <= price);
  assert (forall r:int :: RemCH[pid][r] > 0 ==> r == price - sum(contribution, 1, pid - 1));
  assert RemCH[n][price - sum(contribution, 1, n-1)] > 0;
  assert (exists r:int :: RemCH[pid][r] > 0);
  assert DecCH == (lambda b:bool :: 0);
  assert (forall i:int :: i < pid ==> QuoteCH[i] == (lambda r:int :: 0));

  assert QuoteCH[pid][price] > 0;
  assume RemCH[pid][rem] > 0;

  QuoteCH[pid][price] := QuoteCH[pid][price] - 1;
  RemCH[pid][rem] := RemCH[pid][rem] - 1;

  if (*) { amount := min(wallet, rem); } else { amount := 0; }
  contribution[pid] := amount;

  if (amount == rem)
  {
    DecCH[true] := DecCH[true] + 1;
  }
  else
  {
    DecCH[false] := DecCH[false] + 1;
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 4}
{:IS "MAIN4","INV3"}{:elim "FirstBuyer","FirstBuyer'"}{:elim "MiddleBuyer","MiddleBuyer'"}{:elim "LastBuyer","LastBuyer'"}
MAIN3 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "SellerFinish","FirstBuyer","MiddleBuyer","LastBuyer"} PAs:[PA]int)
modifies QuoteCH;
{
  assert Init(pids, ReqCH, QuoteCH, RemCH, DecCH, contribution);
  QuoteCH := (lambda i:int :: (lambda q:int :: if buyerID(i) && q == price then 1 else 0));
  PAs := MapAddPA4(SellerFinishPA(0), FirstBuyerPA(1), LastBuyerPA(n), (lambda pa:PA :: if is#MiddleBuyerPA(pa) && middleBuyerID(pid#MiddleBuyerPA(pa)) then 1 else 0));
}

procedure {:IS_invariant}{:layer 3}
INV2 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "SellerInit","SellerFinish","FirstBuyer","MiddleBuyer","LastBuyer"} PAs:[PA]int)
modifies ReqCH, QuoteCH;
{
  assert Init(pids, ReqCH, QuoteCH, RemCH, DecCH, contribution);
  if (*)
  {
    ReqCH := 1;
    PAs := MapAddPA4(SellerInitPA(0), FirstBuyerPA(1), LastBuyerPA(n), (lambda pa:PA :: if is#MiddleBuyerPA(pa) && middleBuyerID(pid#MiddleBuyerPA(pa)) then 1 else 0));
  }
  else
  {
    QuoteCH := (lambda i:int :: (lambda q:int :: if buyerID(i) && q == price then 1 else 0));
    PAs := MapAddPA4(SellerFinishPA(0), FirstBuyerPA(1), LastBuyerPA(n), (lambda pa:PA :: if is#MiddleBuyerPA(pa) && middleBuyerID(pid#MiddleBuyerPA(pa)) then 1 else 0));
  }
}

procedure {:atomic}{:layer 3}
SellerInit' ({:linear_in "pid"} pid:int)
returns ({:pending_async "SellerFinish"} PAs:[PA]int)
modifies ReqCH, QuoteCH;
{
  assert sellerID(pid);
  assert QuoteCH == (lambda i:int :: (lambda q:int :: 0)); // To discharge gate failure preservation for FirstBuyer/MiddleBuyer/LastBuyer

  assert ReqCH > 0;
  ReqCH := ReqCH - 1;

  QuoteCH := (lambda i:int :: (lambda q:int :: if buyerID(i) && q == price then QuoteCH[i][q] + 1 else QuoteCH[i][q]));
  PAs := SingletonPA(SellerFinishPA(pid));
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 3}
{:IS "MAIN3","INV2"}{:elim "SellerInit","SellerInit'"}
MAIN2 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "SellerInit","FirstBuyer","MiddleBuyer","LastBuyer"} PAs:[PA]int)
modifies ReqCH;
{
  assert Init(pids, ReqCH, QuoteCH, RemCH, DecCH, contribution);
  ReqCH := 1;
  PAs := MapAddPA4(SellerInitPA(0), FirstBuyerPA(1), LastBuyerPA(n), (lambda pa:PA :: if is#MiddleBuyerPA(pa) && middleBuyerID(pid#MiddleBuyerPA(pa)) then 1 else 0));
}

procedure {:IS_invariant}{:layer 2}
INV1 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "SellerInit","FirstBuyerInit","FirstBuyer","MiddleBuyer","LastBuyer"} PAs:[PA]int)
modifies ReqCH;
{
  assert Init(pids, ReqCH, QuoteCH, RemCH, DecCH, contribution);
  if (*)
  {
    PAs := MapAddPA4(SellerInitPA(0), FirstBuyerInitPA(1), LastBuyerPA(n), (lambda pa:PA :: if is#MiddleBuyerPA(pa) && middleBuyerID(pid#MiddleBuyerPA(pa)) then 1 else 0));
  }
  else
  {
    ReqCH := 1;
    PAs := MapAddPA4(SellerInitPA(0), FirstBuyerPA(1), LastBuyerPA(n), (lambda pa:PA :: if is#MiddleBuyerPA(pa) && middleBuyerID(pid#MiddleBuyerPA(pa)) then 1 else 0));
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}
{:IS "MAIN2","INV1"}{:elim "FirstBuyerInit"}
MAIN1 ({:linear_in "pid"} pids:[int]bool)
returns ({:pending_async "SellerInit","FirstBuyerInit","MiddleBuyer","LastBuyer"} PAs:[PA]int)
{
  assert Init(pids, ReqCH, QuoteCH, RemCH, DecCH, contribution);
  PAs := MapAddPA4(SellerInitPA(0), FirstBuyerInitPA(1), LastBuyerPA(n), (lambda pa:PA :: if is#MiddleBuyerPA(pa) && middleBuyerID(pid#MiddleBuyerPA(pa)) then 1 else 0));
}

procedure {:atomic}{:layer 2,3}
SellerInit ({:linear_in "pid"} pid:int)
returns ({:pending_async "SellerFinish"} PAs:[PA]int)
modifies ReqCH, QuoteCH;
{
  assert sellerID(pid);

  assume ReqCH > 0;
  ReqCH := ReqCH - 1;

  QuoteCH := (lambda i:int :: (lambda q:int :: if buyerID(i) && q == price then QuoteCH[i][q] + 1 else QuoteCH[i][q]));
  PAs := SingletonPA(SellerFinishPA(pid));
}

procedure {:atomic}{:layer 2,5}
SellerFinish ({:linear_in "pid"} pid:int)
modifies DecCH;
{
  var dec:bool;
  assert sellerID(pid);
  assert DecCH[true] > 0 ==> sum(contribution, 1, n) == price;

  assume DecCH[dec] > 0;
  DecCH[dec] := DecCH[dec] - 1;
}

procedure {:atomic}{:layer 2,4}
FirstBuyerInit ({:linear_in "pid"} pid:int)
returns ({:pending_async "FirstBuyer"} PAs:[PA]int)
modifies ReqCH;
{
  assert firstBuyerID(pid);
  ReqCH := ReqCH + 1;
  PAs := SingletonPA(FirstBuyerPA(pid));
}

procedure {:atomic}{:layer 2,4}
FirstBuyer ({:linear_in "pid"} pid:int)
modifies QuoteCH, RemCH, contribution;
{
  var rem:int;
  var amount:int;

  assert firstBuyerID(pid);
  assert (forall q:int :: QuoteCH[pid][q] > 0 ==> q == price);

  assume QuoteCH[pid][price] > 0;
  QuoteCH[pid][price] := QuoteCH[pid][price] - 1;

  rem := price;
  if (*) { amount := min(wallet, rem); } else { amount := 0; }
  contribution[pid] := amount;
  rem := rem - amount;
  RemCH[nextBuyer(pid)][rem] := RemCH[nextBuyer(pid)][rem] + 1;
}

procedure {:atomic}{:layer 2,4}
MiddleBuyer ({:linear_in "pid"} pid:int)
modifies QuoteCH, RemCH, contribution;
{
  var rem:int;
  var amount:int;

  assert middleBuyerID(pid);
  assert (forall q:int :: QuoteCH[pid][q] > 0 ==> q == price);
  assert (forall r:int :: RemCH[pid][r] > 0 ==> 0 <= r && r <= price);

  assume QuoteCH[pid][price] > 0;
  QuoteCH[pid][price] := QuoteCH[pid][price] - 1;

  assume RemCH[pid][rem] > 0;
  RemCH[pid][rem] := RemCH[pid][rem] - 1;

  if (*) { amount := min(wallet, rem); } else { amount := 0; }
  contribution[pid] := amount;
  rem := rem - amount;
  RemCH[nextBuyer(pid)][rem] := RemCH[nextBuyer(pid)][rem] + 1;
}

procedure {:atomic}{:layer 2,4}
LastBuyer ({:linear_in "pid"} pid:int)
modifies QuoteCH, RemCH, DecCH, contribution;
{
  var rem:int;
  var amount:int;

  assert lastBuyerID(pid);
  assert (forall q:int :: QuoteCH[pid][q] > 0 ==> q == price);
  assert (forall r:int :: RemCH[pid][r] > 0 ==> 0 <= r && r <= price);

  assume QuoteCH[pid][price] > 0;
  QuoteCH[pid][price] := QuoteCH[pid][price] - 1;

  assume RemCH[pid][rem] > 0;
  RemCH[pid][rem] := RemCH[pid][rem] - 1;

  if (*) { amount := min(wallet, rem); } else { amount := 0; }
  contribution[pid] := amount;

  if (amount == rem)
  {
      DecCH[true] := DecCH[true] + 1;
  }
  else
  {
    DecCH[false] := DecCH[false] + 1;
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:yields}{:layer 1}{:refines "MAIN1"}
main ({:linear_in "pid"} pids:[int]bool)
requires {:layer 1} Init(pids, ReqCH, QuoteCH, RemCH, DecCH, contribution);
{
  var i:int;
  var {:pending_async}{:layer 1} PAs:[PA]int;
  var {:linear "pid"} pid:int;
  var {:linear "pid"} pids':[int]bool;
  yield; assert {:layer 1} Init(pids, ReqCH, QuoteCH, RemCH, DecCH, contribution);
  pids' := pids;
  call pid, pids' := linear_transfer(0, pids');
  async call sellerInit(pid);
  call pid, pids' := linear_transfer(1, pids');
  async call firstBuyerInit(pid);
  call pid, pids' := linear_transfer(n, pids');
  async call lastBuyer(pid);
  i := 2;
  while (i < n)
  invariant {:layer 0,1}{:terminates} true;
  invariant {:layer 1} 2 <= i && i <= n;
  invariant {:layer 1} (forall ii:int :: middleBuyerID(ii) && ii >= i ==> pids'[ii]);
  invariant {:layer 1} PAs == MapAddPA4(SellerInitPA(0), FirstBuyerInitPA(1), LastBuyerPA(n), (lambda pa:PA :: if is#MiddleBuyerPA(pa) && middleBuyerID(pid#MiddleBuyerPA(pa)) && pid#MiddleBuyerPA(pa) < i then 1 else 0));
  {
    call pid, pids' := linear_transfer(i, pids');
    async call middleBuyer(pid);
    i := i + 1;
  }
  yield;
}

procedure {:yields}{:layer 1}{:refines "SellerInit"}
sellerInit ({:linear_in "pid"} pid:int)
requires {:layer 1} sellerID(pid);
{
  var i:int;
  var {:layer 1} old_QuoteCH:[int][int]int;
  yield;
  call old_QuoteCH := Snapshot_QuoteCH();
  call receive_req();
  async call sellerFinish(pid);
  i := 1;
  while (i <= n)
  invariant {:layer 0,1}{:terminates} true;
  invariant {:layer 1} 1 <= i && i <= n+1;
  invariant {:layer 1} QuoteCH == (lambda ii:int :: (lambda q:int :: if buyerID(ii) && ii < i && q == price then old_QuoteCH[ii][q] + 1 else old_QuoteCH[ii][q]));
  {
    call send_quote(i, price);
    i := i + 1;
  }
  yield;
}

procedure {:yields}{:layer 1}{:refines "SellerFinish"}
sellerFinish ({:linear_in "pid"} pid:int)
requires {:layer 1} sellerID(pid);
{
  var d:bool;
  yield;
  call d := receive_dec();
  if (d)
  {
    call assert_sum();
  }
  yield;
}

procedure {:yields}{:layer 1}{:refines "FirstBuyerInit"}
firstBuyerInit ({:linear_in "pid"} pid:int)
requires {:layer 1} firstBuyerID(pid);
{
  yield;
  call send_req();
  async call firstBuyer(pid);
  yield;
}


procedure {:yields}{:layer 1}{:refines "FirstBuyer"}
firstBuyer ({:linear_in "pid"} pid:int)
requires {:layer 1} firstBuyerID(pid);
{
  var q:int;
  var amount:int;
  yield;
  call q := receive_quote(pid);
  if (*) { amount := min(wallet, q); } else { amount := 0; }
  call set_contribution(pid, amount);
  call send_rem(nextBuyer(pid), q - amount);
  yield;
}

procedure {:yields}{:layer 1}{:refines "MiddleBuyer"}
middleBuyer ({:linear_in "pid"} pid:int)
requires {:layer 1} middleBuyerID(pid);
{
  var q:int;
  var r:int;
  var amount:int;
  yield;
  call q := receive_quote(pid);
  call r := receive_rem(pid);
  if (*) { amount := min(wallet, r); } else { amount := 0; }
  call set_contribution(pid, amount);
  call send_rem(nextBuyer(pid), r - amount);
  yield;
}

procedure {:yields}{:layer 1}{:refines "LastBuyer"}
lastBuyer ({:linear_in "pid"} pid:int)
requires {:layer 1} lastBuyerID(pid);
{
  var q:int;
  var r:int;
  var amount:int;
  yield;
  call q := receive_quote(pid);
  call r := receive_rem(pid);
  if (*) { amount := min(wallet, r); } else { amount := 0; }
  call set_contribution(pid, amount);
  call send_dec(amount == r);
  yield;
}

procedure {:intro}{:layer 1} Snapshot_QuoteCH() returns (snapshot:[int][int]int)
{
  snapshot := QuoteCH;
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

procedure {:left}{:layer 1} SEND_REQ()
modifies ReqCH;
{
  ReqCH := ReqCH + 1;
}

procedure {:right}{:layer 1} RECEIVE_REQ()
modifies ReqCH;
{
  assume ReqCH > 0;
  ReqCH := ReqCH - 1;
}

procedure {:left}{:layer 1} SEND_QUOTE(pid:int, q:int)
modifies QuoteCH;
{
  QuoteCH[pid][q] := QuoteCH[pid][q] + 1;
}

procedure {:right}{:layer 1} RECEIVE_QUOTE(pid:int) returns (q:int)
modifies QuoteCH;
{
  assume QuoteCH[pid][q] > 0;
  QuoteCH[pid][q] := QuoteCH[pid][q] - 1;
}

procedure {:left}{:layer 1} SEND_REM(pid:int, r:int)
modifies RemCH;
{
  RemCH[pid][r] := RemCH[pid][r] + 1;
}

procedure {:right}{:layer 1} RECEIVE_REM(pid:int) returns (r:int)
modifies RemCH;
{
  assume RemCH[pid][r] > 0;
  RemCH[pid][r] := RemCH[pid][r] - 1;
}

procedure {:left}{:layer 1} SEND_DEC(d:bool)
modifies DecCH;
{
  DecCH[d] := DecCH[d] + 1;
}

procedure {:right}{:layer 1} RECEIVE_DEC() returns (d:bool)
modifies DecCH;
{
  assume DecCH[d] > 0;
  DecCH[d] := DecCH[d] - 1;
}

procedure {:yields}{:layer 0}{:refines "SET_CONTRIBUTION"} set_contribution({:linear "pid"} pid:int, c:int);
procedure {:yields}{:layer 0}{:refines "ASSERT_SUM"} assert_sum();
procedure {:yields}{:layer 0}{:refines "SEND_REQ"} send_req();
procedure {:yields}{:layer 0}{:refines "RECEIVE_REQ"} receive_req();
procedure {:yields}{:layer 0}{:refines "SEND_QUOTE"} send_quote(pid:int, q:int);
procedure {:yields}{:layer 0}{:refines "RECEIVE_QUOTE"} receive_quote(pid:int) returns (q:int);
procedure {:yields}{:layer 0}{:refines "SEND_REM"} send_rem(pid:int, r:int);
procedure {:yields}{:layer 0}{:refines "RECEIVE_REM"} receive_rem(pid:int) returns (r:int);
procedure {:yields}{:layer 0}{:refines "SEND_DEC"} send_dec(d:bool);
procedure {:yields}{:layer 0}{:refines "RECEIVE_DEC"} receive_dec() returns (d:bool);

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
