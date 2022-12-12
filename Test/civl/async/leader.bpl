// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const N : int;
axiom N > 0;

type Pid = int;
function is_pid (pid:Pid) : bool { 1 <= pid && pid <= N }

type {:datatype} {:linear "Perm"} Perm;
function {:constructor} Perm (s:Pid, r:Pid) : Perm;

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

procedure {:atomic}{:layer 2} main_atomic ({:linear_in "Perm"} perms:[Perm]bool)
modifies col_dom, col_val, dec_dom, dec_val;
{
  havoc dec_dom, dec_val;
  assume all_decided(init_val, dec_dom, dec_val);
}

procedure {:yields}{:layer 1}{:refines "main_atomic"} main ({:linear_in "Perm"} perms:[Perm]bool)
requires {:layer 1} perms == all_perms();
ensures {:layer 1} all_decided(init_val, dec_dom, dec_val);
{
  var s:int;
  var {:linear "Perm"} perms':[Perm]bool;
  var {:linear "Perm"} perms'':[Perm]bool;
  s := 1;
  perms' := perms;
  while (s <= N)
  invariant {:layer 1}{:cooperates} true;
  invariant {:layer 1} perms' == s_perms_geq(s);
  invariant {:layer 1} inv_val(s, init_val, col_dom, col_val);
  invariant {:layer 1} s > N ==> all_decided(init_val, dec_dom, dec_val);
  {
    call perms',perms'' := split_perms_sender(s, perms');
    async call {:sync} P(s, perms'');
    s := s + 1;
  }
}

procedure {:yields}{:layer 1}{:left} P (s:int, {:linear_in "Perm"} perms:[Perm]bool)
requires {:layer 1} perms == s_perms_eq(s);
requires {:layer 1} inv_val(s, init_val, col_dom, col_val);
ensures  {:layer 1} inv_val(s+1, init_val, col_dom, col_val);
ensures  {:layer 1} s == N ==> all_decided(init_val, dec_dom, dec_val);
modifies col_dom, col_val, dec_dom, dec_val;
{
  var r:int;
  var v:int;
  var {:linear "Perm"} p:Perm;
  var {:linear "Perm"} perms':[Perm]bool;

  perms' := perms;
  r := 1;
  call v := read_init_val(s);
  while (r <= N)
  invariant {:layer 1}{:cooperates} true;
  invariant {:layer 1} perms' == s_r_perms_geq(s,r);
  invariant {:layer 1} inv_val'(s, r, init_val, col_dom, col_val);
  invariant {:layer 1} s == N ==> all_decided'(r, init_val, dec_dom, dec_val);
  {
    call perms',p := split_perms_receiver(s,r,perms');
    async call {:sync} Q(r, s, v, p);
    r := r + 1;
  }
}

procedure {:left}{:layer 1} Q_atomic (r:int, s:int, v:int, {:linear_in "Perm"} p:Perm)
modifies col_dom, col_val, dec_dom, dec_val;
{
  assert is_perm(s,r,p);
  col_dom[r][s] := true;
  col_val[r][s] := v;
  if ((forall pid:int :: is_pid(pid) ==> col_dom[r][pid])) {
    dec_dom[r] := true;
    dec_val[r] := decision_function(col_val[r]);
  }
}

procedure {:both}{:layer 1} read_init_val_atomic (pid:Pid) returns (v:int)
{
  v := init_val[pid];
}

procedure {:yields}{:layer 0}{:refines "Q_atomic"} Q (r:int, s:int, v:int, {:linear_in "Perm"} p:Perm);
procedure {:yields}{:layer 0}{:refines "read_init_val_atomic"} read_init_val (pid:Pid) returns (v:int);

// ###########################################################################
// Linear permissions

function {:inline} all_perms () : [Perm]bool { (lambda p:Perm :: is_pid(p->s) && is_pid(p->r)) }
function {:inline} s_perms_eq (s:Pid) : [Perm]bool { (lambda p:Perm :: p->s == s && is_pid(p->r)) }
function {:inline} s_perms_geq (s:Pid) : [Perm]bool { (lambda p:Perm :: is_pid(p->s) && is_pid(p->r) && p->s >= s) }
function {:inline} s_r_perms_geq (s:Pid, r:Pid) : [Perm]bool { (lambda p:Perm :: p->s == s && is_pid(p->r) && p->r >= r) }

procedure {:yields}{:layer 1}{:both} split_perms_sender (s:Pid, {:linear_in "Perm"} perms_in:[Perm]bool) returns ({:linear "Perm"} perms_out_1:[Perm]bool, {:linear "Perm"} perms_out_2:[Perm]bool);
requires {:layer 1} perms_in == s_perms_geq(s);
ensures {:layer 1} perms_out_1 == s_perms_geq(s+1);
ensures {:layer 1} perms_out_2 == s_perms_eq(s);

procedure {:yields}{:layer 1}{:both} split_perms_receiver (s:Pid, r:Pid, {:linear_in "Perm"} perms_in:[Perm]bool) returns ({:linear "Perm"} perms_out_1:[Perm]bool, {:linear "Perm"} perms_out_2:Perm);
requires {:layer 1} perms_in ==  s_r_perms_geq(s,r);
ensures {:layer 1} perms_out_1 == s_r_perms_geq(s,r+1);
ensures {:layer 1} is_perm(s,r,perms_out_2);
