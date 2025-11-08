// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const MultisetEmpty: [val]int;
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

/*
This is a two-layered proof of broadcast consensus.
In the first layer, the Broadcast and Collect yield procedures performed by each process are
converted into BROADCAST and COLLECT atomic actions, respectively.
In the second layer, the body of Main comprising the broadcast loop followed by the collect
loop are summarized.
This summarization is enabled by a precondition on COLLECT that holds only after the
broadcast loop is finished.
This precondition is used to show that COLLECT is a left mover.
*/

// processes deposit Broadcast and Collect permissions in this global
// variable once they are finished with the respective operations
var {:layer 0,2} {:linear} usedPermissions: Set Permission;

// array of values in the processes
// each process broadcasts its value to all other processes
var {:layer 0,2} value: [pid]val;

// input channels for each process
// each channel is modeled as a multiset
var {:layer 0,1} channels: [pid][val]int;

// processes store their consensus decision in this array
// goal of verification is to prove that all values in decision are identical at the end
var {:layer 0,2} decision: [pid]val;

// multiset of values in the value array
// abstraction of channels in program at layer 2
var {:layer 1,2} values: [val]int;

function max(values:[val]int) : val;
function card(values:[val]int) : int;

axiom card(MultisetEmpty) == 0;
axiom (forall values:[val]int, v:val, x:int :: card(values[v := x]) == card(values) + x - values[v]);
axiom (forall m:[val]int, m':[val]int :: MultisetSubsetEq(m, m') && card(m) == card(m') ==> m == m');

axiom (forall v:val :: max(MultisetSingleton(v)) == v);
axiom (forall values:[val]int, v:val, x:int :: x > 0 ==> max(values[v := x]) == (if v > max(values) then v else max(values)));

function value_card(v:val, value:[pid]val, j:pid) : int
{
  if j < 1 then
    0
  else if value[j] == v then
    value_card(v, value, j-1) + 1
  else
    value_card(v, value, j-1)
}

////////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 1} YieldCollect();
preserves (forall i:pid :: MultisetSubsetEq(MultisetEmpty, channels[i]) && MultisetSubsetEq(channels[i], values));

invariant {:layer 2} CollectPre();
preserves values == (lambda v:val :: value_card(v, value, n));
preserves card(values) == n;
preserves MultisetSubsetEq(MultisetEmpty, values);
preserves (forall q: Permission:: q is Broadcast && IsPid(q->i) ==> Set_Contains(usedPermissions, q));

////////////////////////////////////////////////////////////////////////////////

yield left procedure {:layer 2} Main({:linear_in} ps: Set Permission)
requires {:layer 1} (forall ii:pid :: channels[ii] == MultisetEmpty);
requires {:layer 1,2} ps->val == (lambda {:pool "A"} p: Permission ::IsPid(p->i));
requires {:layer 1,2} values == MultisetEmpty;
requires {:layer 1,2} usedPermissions == Set_Empty();
ensures {:layer 2} (forall j: pid:: IsPid(j) ==> decision[j] == max((lambda v: val:: value_card(v, value, n))));
modifies values, usedPermissions, decision;
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
  invariant {:layer 2} MultisetSubsetEq(MultisetEmpty, values) && values == (lambda v: val:: value_card(v, value, i-1)) && card(values) == i-1;
  invariant {:layer 2} Set((lambda p: Permission:: p is Broadcast && IsPid(p->i))) == Set_Union(usedPermissions, psb);
  {
    call s := One_Get(psb, Broadcast(i));
    async call {:sync} Broadcast(s, i);
    i := i + 1;
  }

  assert {:layer 2} MultisetSubsetEq(MultisetEmpty, values) && values == (lambda v: val:: value_card(v, value, n)) && card(values) == n;

  i := 1;
  while (i <= n)
  invariant {:layer 1,2} 1 <= i && i <= n + 1;
  invariant {:layer 1,2} psc->val == (lambda p: Permission:: p is Collect && i <= p->i && p->i <= n);
  invariant {:layer 2} (forall q: Permission:: q is Broadcast && IsPid(q->i) ==> Set_Contains(usedPermissions, q));
  invariant {:layer 2} (forall j: pid:: 1 <= j && j < i ==> decision[j] == max(values));
  {
    call r := One_Get(psc, Collect(i));
    async call {:sync} Collect(r, i);
    i := i + 1;
  }
}

left action {:layer 2} BROADCAST({:linear_in} p: One Permission, i:pid)
{
  assert IsPid(i) && p->val == Broadcast(i);
  assume {:add_to_pool "A", Broadcast(i)} true;
  values := values[value[i] := values[value[i]] + 1];
  call One_Put(usedPermissions, p);
}

yield procedure {:layer 1} Broadcast({:linear_in} p: One Permission, i:pid)
refines BROADCAST;
requires {:layer 1} IsPid(i) && p->val == Broadcast(i);
{
  var j: pid;
  var v: val;
  var {:layer 1} old_channels: [pid][val]int;

  call {:layer 1} old_channels := Copy(channels);
  call v := get_value(i);
  j := 1;
  while (j <= n)
  invariant {:layer 1} 1 <= j && j <= n+1;
  invariant {:layer 1} channels == 
    (lambda jj: pid :: (if IsPid(jj) && jj < j then MultisetPlus(old_channels[jj], MultisetSingleton(value[p->val->i])) else old_channels[jj]));
  {
    call send(v, j);
    j := j + 1;
  }
  call {:layer 1} values :=  Copy(values[value[i] := values[value[i]] + 1]);
  call release_permission(p);
}

left action {:layer 2} COLLECT({:linear_in} p: One Permission, i:pid)
requires call CollectPre();
{
  var received_values:[val]int;
  assert IsPid(i) && p->val == Collect(i);
  assume card(received_values) == n;
  assume MultisetSubsetEq(MultisetEmpty, received_values);
  assume MultisetSubsetEq(received_values, values);
  decision[i] := max(received_values);
  call One_Put(usedPermissions, p);
}

yield procedure {:layer 1} Collect({:linear_in} p: One Permission, i:pid)
refines COLLECT;
requires call YieldCollect();
requires {:layer 1} IsPid(i) && p->val == Collect(i);
{
  var j: pid;
  var d: val;
  var v: val;
  var {:layer 1} received_values: [val]int;
  var {:layer 1} old_channels: [pid][val]int;

  call {:layer 1} old_channels := Copy(channels);
  call d := receive(i);
  received_values := MultisetSingleton(d);
  j := 2;
  while (j <= n)
  invariant {:layer 1} 2 <= j && j <= n + 1;
  invariant {:layer 1} card(received_values) == j - 1;
  invariant {:layer 1} MultisetSubsetEq(MultisetEmpty, received_values);
  invariant {:layer 1} MultisetSubsetEq(received_values, old_channels[i]);
  invariant {:layer 1} channels == old_channels[i := MapSub(old_channels[i], received_values)];
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

yield procedure {:layer 0} get_value(i:pid) returns (v:val);
refines both action {:layer 1} _ {
  v := value[i];
}

yield procedure {:layer 0} set_decision({:linear_in} p: One Permission, d:val);
refines both action {:layer 1} _ {
  assert p->val is Collect;
  decision[p->val->i] := d;
  call One_Put(usedPermissions, p);
}

yield procedure {:layer 0} send(v:val, i:pid);
refines left action {:layer 1} _ {
  channels[i][v] := channels[i][v] + 1;
}

yield procedure {:layer 0} receive(i:pid) returns (v:val);
refines right action {:layer 1} _ {
  assume channels[i][v] > 0;
  channels[i][v] := channels[i][v] - 1;
}

yield procedure {:layer 0} release_permission({:linear_in} p: One Permission);
refines both action {:layer 1} _ {
  call One_Put(usedPermissions, p);
}
