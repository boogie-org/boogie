// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,3} val_a : int;
var {:layer 0,3} val_b : int;

// ###########################################################################
// Linear permissions

function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;

function {:inline} {:linear "lin"} LinCollector(x : int) : [int]bool
{ MapConstBool(false)[x := true] }

function {:inline} perm (p : int) : bool
{ p == 0 }

// ###########################################################################
// Main (process A sends initial proposal)

procedure {:atomic} {:layer 3} atomic_agree ({:linear_in "lin"} p : int)
modifies val_a, val_b;
{
  var val_a_new : int;
  var val_b_new : int;
  assume val_a_new == val_b_new;
  val_a := val_a_new;
  val_b := val_b_new;
}

procedure {:yields} {:layer 2} {:refines "atomic_agree"} main ({:linear_in "lin"} p : int)
requires {:layer 2} perm(p);
{
  var val_a_local : int;
  yield; assert {:layer 2} perm(p);
  call val_a_local := get_val_a_perm(p);
  async call propose_by_a(val_a_local, p);
  yield;
}

// ###########################################################################
// Event handlers of process B

procedure {:yields} {:layer 2} {:left} {:terminates}  propose_by_a (val : int, {:linear_in "lin"} p : int)
requires {:layer 2} perm(p);
requires {:layer 2} val_a == val;
ensures {:layer 2} val_a == val_b;
modifies val_a, val_b;
{
  var val_b_local : int;
  
  if (*)
  {
    call set_val_b_perm(val, p);
    async call ack_by_b(p);
  }
  else
  {
    call set_val_b_perm(val_b_local, p);
    async call propose_by_b(val_b_local, p);
  }

  call dummy_1();
}

procedure {:yields} {:layer 2} {:left} ack_by_a({:linear_in "lin"} p : int)
requires {:layer 2} perm(p);
requires {:layer 2} val_a == val_b;
ensures {:layer 2} val_a == val_b;
{
  call dummy_1();
}

// ###########################################################################
// Event handlers of process A

procedure {:yields} {:layer 2} {:left} {:terminates} propose_by_b (val : int, {:linear_in "lin"} p : int)
requires {:layer 2} perm(p);
requires {:layer 2} val_b == val;
ensures {:layer 2} val_a == val_b;
modifies val_a, val_b;
{
  var val_a_local : int;
  
  if (*)
  {
    call set_val_a_perm(val, p);
    async call ack_by_a(p);
  }
  else
  {
    call set_val_a_perm(val_a_local, p);
    async call propose_by_a(val_a_local, p);
  }

  call dummy_1();
}

procedure {:yields} {:layer 2} {:left} ack_by_b({:linear_in "lin"} p : int)
requires {:layer 2} perm(p);
requires {:layer 2} val_a == val_b;
ensures {:layer 2} val_a == val_b;
{
  call dummy_1();
}

// ###########################################################################
// Dummy procedure to satisfy yield checker for mover procedures

procedure {:yields} {:layer 1} dummy_1 ();

// ###########################################################################
// Abstracted atomic actions with permissions

procedure {:both} {:layer 2} atomic_get_val_a_perm ({:linear "lin"} p : int) returns (ret : int)
{ assert perm(p); ret := val_a; }

procedure {:both} {:layer 2} atomic_set_val_a_perm (val : int, {:linear "lin"} p : int)
modifies val_a;
{ assert perm(p); val_a := val; }

procedure {:both} {:layer 2} atomic_set_val_b_perm (val : int, {:linear "lin"} p : int)
modifies val_b;
{ assert perm(p); val_b := val; }

procedure {:yields} {:layer 1} {:refines "atomic_get_val_a_perm"} get_val_a_perm ({:linear "lin"} p : int) returns (ret : int)
{ yield; call ret := get_val_a(); yield; }
procedure {:yields} {:layer 1} {:refines "atomic_set_val_a_perm"} set_val_a_perm (val : int, {:linear "lin"} p : int)
{ yield; call set_val_a(val); yield; }
procedure {:yields} {:layer 1} {:refines "atomic_set_val_b_perm"} set_val_b_perm (val : int, {:linear "lin"} p : int)
{ yield; call set_val_b(val); yield; }

// ###########################################################################
// Primitive atomic actions

procedure {:atomic} {:layer 1} atomic_get_val_a () returns (ret : int)
{ ret := val_a; }

procedure {:atomic} {:layer 1} atomic_set_val_a (val : int)
modifies val_a;
{ val_a := val; }

procedure {:atomic} {:layer 1} atomic_set_val_b (val : int)
modifies val_b;
{ val_b := val; }

procedure {:yields} {:layer 0} {:refines "atomic_get_val_a"} get_val_a () returns (ret : int);
procedure {:yields} {:layer 0} {:refines "atomic_set_val_a"} set_val_a (val : int);
procedure {:yields} {:layer 0} {:refines "atomic_set_val_b"} set_val_b (val : int);
