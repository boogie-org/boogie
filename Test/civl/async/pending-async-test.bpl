// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,3} x:int;  

procedure {:both}{:layer 3} Client_atomic ()
modifies x;
{ x := x + 1; }

procedure {:yields}{:layer 2}{:refines "Client_atomic"} Client ()
{
  yield;
  call Service();
  yield;
}

procedure {:atomic}{:layer 1,2} Service_atomic ()
{ async call Callback(); }

procedure {:yields}{:layer 0}{:refines "Service_atomic"} Service ()
{
  yield;
  async call Callback();
  yield;
}

procedure {:both}{:layer 2} Callback_atomic ()
modifies x;
{ x := x + 1; }

procedure {:yields}{:layer 1}{:refines "Callback_atomic"} Callback ();
