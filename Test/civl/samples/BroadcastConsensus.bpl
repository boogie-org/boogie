// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const MultisetEmpty:[val]int;
axiom MultisetEmpty == MapConst(0);

function {:inline} MultisetSingleton(v:val) : [val]int
{
  MultisetEmpty[v := 1]
}

function {:inline} MultisetSubsetEq(a:[val]int, b:[val]int) : bool
{
  MapLe(a, b) == MapConst(true)
}

function {:inline} MultisetPlus(a:[val]int, b:[val]int) : [val]int
{
  MapAdd(a, b)
}

const n:int;
axiom n >= 1;

type val = int;
type pid = int;

datatype Permission {
  Broadcast(i: int),
  Collect(i: int)
}

function {:inline} IsPid(i:int) : bool { 1 <= i && i <= n }

////////////////////////////////////////////////////////////////////////////////

var {:layer 0,1} CH_low:[pid][val]int;
var {:layer 1,2} CH:[val]int;
var {:layer 0,2} {:linear} usedPermissions: Set Permission;
var {:layer 0,2} value:[pid]val;
var {:layer 0,2} decision:[pid]val;

function max(CH:[val]int) : val;
function card(CH:[val]int) : int;

axiom card(MultisetEmpty) == 0;
axiom (forall CH:[val]int, v:val, x:int :: card(CH[v := x]) == card(CH) + x - CH[v]);
axiom (forall m:[val]int, m':[val]int :: MultisetSubsetEq(m, m') && card(m) == card(m') ==> m == m');

axiom (forall v:val :: max(MultisetSingleton(v)) == v);
axiom (forall CH:[val]int, v:val, x:int :: x > 0 ==> max(CH[v := x]) == (if v > max(CH) then v else max(CH)));

function value_card(v:val, value:[pid]val, j:pid) : int
{
  if j < 1 then
    0
  else
    if value[j] == v then
      value_card(v, value, j-1) + 1
    else
      value_card(v, value, j-1)
}

////////////////////////////////////////////////////////////////////////////////

invariant {:layer 2} YieldCollect();
preserves CH == (lambda v:val :: value_card(v, value, n));
preserves card(CH) == n;
preserves MultisetSubsetEq(MultisetEmpty, CH);
preserves (forall q: Permission:: q is Broadcast && IsPid(q->i) ==> Set_Contains(usedPermissions, q));

yield invariant {:layer 1} YieldInv();
preserves Inv(CH_low, CH);

function {:inline} Inv(CH_low:[pid][val]int, CH:[val]int) : bool
{
  (forall i:pid :: MultisetSubsetEq(MultisetEmpty, CH_low[i]) && MultisetSubsetEq(CH_low[i], CH))
}

yield invariant {:layer 1} YieldInit#1({:linear} ps: Set Permission);
preserves ps->val == (lambda {:pool "A"} p: Permission ::IsPid(p->i));
preserves (forall ii:pid :: CH_low[ii] == MultisetEmpty);
preserves CH == MultisetEmpty;
preserves usedPermissions == Set_Empty();

yield invariant {:layer 2} YieldInit#2({:linear} ps: Set Permission);
preserves ps->val == (lambda {:pool "A"} p: Permission ::IsPid(p->i));
preserves CH == MultisetEmpty;
preserves usedPermissions == Set_Empty();

yield left procedure {:layer 2} Main({:linear_in} ps: Set Permission)
requires call YieldInit#1(ps);
requires call YieldInit#2(ps);
ensures {:layer 2} (forall j: pid:: 1 <= j && j <= n ==> decision[j] == max((lambda v: val:: value_card(v, value, n))));
modifies CH, usedPermissions, decision;
{
  var i: pid;
  var {:linear} s: One Permission;
  var {:linear} r: One Permission;
  var {:linear} psb, psc: Set Permission;

  assume {:add_to_pool "A", Broadcast(1)} true;
  psc := ps;
  call psb := Set_Get(psc, (lambda p: Permission:: p is Broadcast && IsPid(p->i)));
  i := 1;
  while (i <= n)
  invariant {:layer 1,2} 1 <= i && i <= n + 1;
  invariant {:layer 1,2} psb->val == (lambda p: Permission:: p is Broadcast && i <= p->i && p->i <= n);
  invariant {:layer 2} MultisetSubsetEq(MultisetEmpty, CH) && CH == (lambda v: val:: value_card(v, value, i-1)) && card(CH) == i-1;
  invariant {:layer 2} Set((lambda p: Permission:: p is Broadcast && IsPid(p->i))) == Set_Union(usedPermissions, psb);
  {
    call s := One_Get(psb, Broadcast(i));
    async call {:sync} Broadcast(s, i);
    i := i + 1;
  }

  assert {:layer 2} MultisetSubsetEq(MultisetEmpty, CH) && CH == (lambda v: val:: value_card(v, value, n)) && card(CH) == n;

  i := 1;
  while (i <= n)
  invariant {:layer 1,2} 1 <= i && i <= n + 1;
  invariant {:layer 1,2} psc->val == (lambda p: Permission:: p is Collect && i <= p->i && p->i <= n);
  invariant {:layer 2} (forall q: Permission:: q is Broadcast && IsPid(q->i) ==> Set_Contains(usedPermissions, q));
  invariant {:layer 2} (forall j: pid:: 1 <= j && j < i ==> decision[j] == max(CH));
  {
    call r := One_Get(psc, Collect(i));
    async call {:sync} Collect(r, i);
    i := i + 1;
  }
}

left action {:layer 2} BROADCAST({:linear_in} p: One Permission, i:pid)
modifies CH;
{
  assert IsPid(i) && p->val == Broadcast(i);
  assume {:add_to_pool "A", Broadcast(i)} true;
  CH := CH[value[i] := CH[value[i]] + 1];
  call One_Put(usedPermissions, p);
}

yield procedure {:layer 1} Broadcast({:linear_in} p: One Permission, i:pid)
refines BROADCAST;
requires {:layer 1} IsPid(i) && p->val == Broadcast(i);
{
  var j: pid;
  var v: val;
  var {:layer 1} old_CH_low: [pid][val]int;

  call {:layer 1} old_CH_low := Copy(CH_low);
  call v := get_value(i);
  j := 1;
  while (j <= n)
  invariant {:layer 1} 1 <= j && j <= n+1;
  invariant {:layer 1} CH_low == (lambda jj: pid :: (if IsPid(jj) && jj < j then MultisetPlus(old_CH_low[jj], MultisetSingleton(value[p->val->i])) else old_CH_low[jj]));
  {
    call send(v, j);
    j := j + 1;
  }
  call {:layer 1} CH :=  Copy(CH[value[i] := CH[value[i]] + 1]);
  call release_permission(p);
}

left action {:layer 2} COLLECT({:linear_in} p: One Permission, i:pid)
modifies decision;
requires call YieldCollect();
{
  var received_values:[val]int;
  assert IsPid(i) && p->val == Collect(i);
  assume card(received_values) == n;
  assume MultisetSubsetEq(MultisetEmpty, received_values);
  assume MultisetSubsetEq(received_values, CH);
  decision[i] := max(received_values);
  call One_Put(usedPermissions, p);
}

yield procedure {:layer 1} Collect({:linear_in} p: One Permission, i:pid)
refines COLLECT;
requires call YieldInv();
requires {:layer 1} IsPid(i) && p->val == Collect(i);
{
  var j: pid;
  var d: val;
  var v: val;
  var {:layer 1} received_values: [val]int;
  var {:layer 1} old_CH_low: [pid][val]int;

  call {:layer 1} old_CH_low := Copy(CH_low);
  call d := receive(i);
  received_values := MultisetSingleton(d);
  j := 2;
  while (j <= n)
  invariant {:layer 1} 2 <= j && j <= n + 1;
  invariant {:layer 1} card(received_values) == j - 1;
  invariant {:layer 1} MultisetSubsetEq(MultisetEmpty, received_values);
  invariant {:layer 1} MultisetSubsetEq(received_values, old_CH_low[i]);
  invariant {:layer 1} CH_low == old_CH_low[i := MapSub(old_CH_low[i], received_values)];
  invariant {:layer 1} d == max(received_values);
  {
    call v := receive(i);
    if (v > d) { d := v; }
    received_values[v] := received_values[v] + 1;
    j := j + 1;
  }
  call set_decision(p, d);
}

////////////////////////////////////////////////////////////////////////////////

both action {:layer 1} GET_VALUE(i:pid) returns (v:val)
{
  v := value[i];
}

both action {:layer 1} SET_DECISION({:linear_in} p: One Permission, d:val)
modifies decision, usedPermissions;
{
  assert p->val is Collect;
  decision[p->val->i] := d;
  call One_Put(usedPermissions, p);
}

left action {:layer 1} SEND(v:val, i:pid)
modifies CH_low;
{
  CH_low[i][v] := CH_low[i][v] + 1;
}

right action {:layer 1} RECEIVE(i:pid) returns (v:val)
modifies CH_low;
{
  assume CH_low[i][v] > 0;
  CH_low[i][v] := CH_low[i][v] - 1;
}

yield procedure {:layer 0} get_value(i:pid) returns (v:val);
refines GET_VALUE;

yield procedure {:layer 0} set_decision({:linear_in} p: One Permission, d:val);
refines SET_DECISION;

yield procedure {:layer 0} send(v:val, i:pid);
refines SEND;

yield procedure {:layer 0} receive(i:pid) returns (v:val);
refines RECEIVE;

yield procedure {:layer 0} release_permission({:linear_in} p: One Permission);
refines both action {:layer 1} _ {
  call One_Put(usedPermissions, p);
}
