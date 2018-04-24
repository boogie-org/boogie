// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var{:layer 20,40} x:int;

procedure{:both}{:layer 21,25} atomic_p_gt1_lower()
modifies x;
{ x := x + 1; }

procedure{:yields}{:layer 20} {:refines "atomic_p_gt1_lower"} p_gt1_lower();

procedure{:both}{:layer 26,40} atomic_p_gt1()
modifies x;
{ x := x + 1; }
  
procedure{:yields}{:layer 25} {:refines "atomic_p_gt1"} p_gt1()  
{
  yield;
  call p_gt1_lower();
  yield;
}

procedure{:both}{:layer 21,40} atomic_p_gt2()
{ assert x == 0; }

procedure{:yields}{:layer 20} {:refines "atomic_p_gt2"} p_gt2();

