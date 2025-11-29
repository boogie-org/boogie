// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const N : int;
axiom N > 0;

type Pid = int;
function is_pid (pid:Pid) : bool { 1 <= pid && pid <= N }

datatype Perm { Perm (s:Pid, r:Pid) }

function {:inline} is_perm (s:Pid, r:Pid, p:Perm) : bool
{ p == Perm(s, r) && is_pid(p->s) && is_pid(p->r) }

function decision_function ([int]int) : int;
axiom (forall x:[int]int, y:[int]int :: (forall pid:int :: is_pid(pid) ==> x[pid] == y[pid]) ==> decision_function(x) == decision_function(y));

// ###########################################################################
// Global shared variables

var {:layer 0,2} init_val:[int]int;      // initial values of i (immutable)
var {:layer 0,1} col_dom:[int][int]bool; // i received from j?
var {:layer 0,1} col_val:[int][int]int;  // value i received from j
var {:layer 0,2} dec_dom:[int]bool;      // i decided?
var {:layer 0,2} dec_val:[int]int;       // decided value of i

// ###########################################################################
// Definitions for specs

function {:inline} inv_val (s_bound:int, init_val:[int]int, col_dom:[int][int]bool, col_val:[int][int]int) : bool
{
  inv_val'(s_bound, 0, init_val, col_dom, col_val)
}

function {:inline} inv_val' (s_bound:int, r_bound:int, init_val:[int]int, col_dom:[int][int]bool, col_val:[int][int]int) : bool
{
  (forall s:int,r:int :: is_pid(s) && s < s_bound && is_pid(r) ==> col_dom[r][s] && col_val[r][s] == init_val[s]) &&
  (forall r:int :: is_pid(r) && r < r_bound ==> col_dom[r][s_bound] && col_val[r][s_bound] == init_val[s_bound])
}

function {:inline} all_decided (init_val:[int]int, dec_dom:[int]bool, dec_val:[int]int) : bool
{
  all_decided'(N+1, init_val, dec_dom, dec_val)
}

function {:inline} all_decided' (r_bound:int, init_val:[int]int, dec_dom:[int]bool, dec_val:[int]int) : bool
{
  (forall r:int :: is_pid(r) && r < r_bound ==> dec_dom[r] && dec_val[r] == decision_function(init_val))
}

// ###########################################################################
// Main

atomic action {:layer 2} main_atomic ({:linear_in} perms: Set (One Perm))
modifies dec_dom, dec_val;
{
  havoc dec_dom, dec_val;
  assume all_decided(init_val, dec_dom, dec_val);
}

yield invariant {:layer 1} YieldAllDecided();
preserves all_decided(init_val, dec_dom, dec_val);

yield procedure {:layer 1}
main ({:linear_in} perms: Set (One Perm))
refines main_atomic;
requires {:layer 1} perms->val == all_perms();
ensures call YieldAllDecided();
{
  var s:int;
  var perms': Set (One Perm);
  var perms'': Set (One Perm);
  s := 1;
  perms' := perms;
  while (s <= N)
  invariant {:layer 1} perms'->val == s_perms_geq(s);
  invariant {:layer 1} inv_val(s, init_val, col_dom, col_val);
  invariant {:layer 1} s > N ==> all_decided(init_val, dec_dom, dec_val);
  {
    call perms',perms'' := split_perms_sender(s, perms');
    async call {:sync} P(s, perms'');
    s := s + 1;
  }
}

yield left procedure {:layer 1} P (s:int, {:linear_in} perms: Set (One Perm))
requires {:layer 1} perms->val == s_perms_eq(s);
requires {:layer 1} inv_val(s, init_val, col_dom, col_val);
ensures  {:layer 1} inv_val(s+1, init_val, col_dom, col_val);
ensures  {:layer 1} s == N ==> all_decided(init_val, dec_dom, dec_val);
modifies col_dom, col_val, dec_dom, dec_val;
{
  var r:int;
  var v:int;
  var p: One Perm;
  var perms': Set (One Perm);

  perms' := perms;
  r := 1;
  call v := read_init_val(s);
  while (r <= N)
  invariant {:layer 1} perms'->val == s_r_perms_geq(s,r);
  invariant {:layer 1} inv_val'(s, r, init_val, col_dom, col_val);
  invariant {:layer 1} s == N ==> all_decided'(r, init_val, dec_dom, dec_val);
  {
    call perms',p := split_perms_receiver(s,r,perms');
    async call {:sync} Q(r, s, v, p);
    r := r + 1;
  }
}

left action {:layer 1} Q_atomic (r:int, s:int, v:int, {:linear_in} p: One Perm)
modifies col_dom, col_val, dec_dom, dec_val;
{
  assert is_perm(s,r,p->val);
  col_dom[r][s] := true;
  col_val[r][s] := v;
  if ((forall pid:int :: is_pid(pid) ==> col_dom[r][pid])) {
    dec_dom[r] := true;
    dec_val[r] := decision_function(col_val[r]);
  }
}

both action {:layer 1} read_init_val_atomic (pid:Pid) returns (v:int)
{
  v := init_val[pid];
}

yield procedure {:layer 0} Q (r:int, s:int, v:int, {:linear_in} p: One Perm);
refines Q_atomic;

yield procedure {:layer 0} read_init_val (pid:Pid) returns (v:int);
refines read_init_val_atomic;

// ###########################################################################
// Linear permissions

function {:inline} all_perms () : [One Perm]bool { (lambda p:One Perm :: is_pid(p->val->s) && is_pid(p->val->r)) }
function {:inline} s_perms_eq (s:Pid) : [One Perm]bool { (lambda p:One Perm :: p->val->s == s && is_pid(p->val->r)) }
function {:inline} s_perms_geq (s:Pid) : [One Perm]bool { (lambda p:One Perm :: is_pid(p->val->s) && is_pid(p->val->r) && p->val->s >= s) }
function {:inline} s_r_perms_geq (s:Pid, r:Pid) : [One Perm]bool { (lambda p:One Perm :: p->val->s == s && is_pid(p->val->r) && p->val->r >= r) }

yield both procedure {:layer 1} split_perms_sender (s:Pid, {:linear_in} perms_in: Set (One Perm)) returns ({:linear} perms_out_1: Set (One Perm), {:linear} perms_out_2: Set (One Perm));
requires {:layer 1} perms_in->val == s_perms_geq(s);
ensures {:layer 1} perms_out_1->val == s_perms_geq(s+1);
ensures {:layer 1} perms_out_2->val == s_perms_eq(s);

yield both procedure {:layer 1} split_perms_receiver (s:Pid, r:Pid, {:linear_in} perms_in: Set (One Perm)) returns ({:linear} perms_out_1: Set (One Perm), {:linear} perms_out_2: One Perm);
requires {:layer 1} perms_in->val ==  s_r_perms_geq(s,r);
ensures {:layer 1} perms_out_1->val == s_r_perms_geq(s,r+1);
ensures {:layer 1} is_perm(s,r,perms_out_2->val);
