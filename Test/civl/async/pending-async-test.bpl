// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,3} x:int;

type {:pending_async}{:datatype} PA;
function {:pending_async "A_Callback"}{:constructor} A_Callback() : PA;

procedure {:both}{:layer 3} A_Client ()
modifies x;
{ x := x + 1; }
procedure {:yields}{:layer 2}{:refines "A_Client"} Client ()
{
  call Service();
}

procedure {:atomic}{:layer 2} A_Service ()
modifies x;
{ x := x + 1; }

procedure {:IS_invariant}{:layer 1} INV() returns ({:pending_async "A_Callback"} PAs: [PA]int)
modifies x;
{
  PAs := MapConst(0);
  if (*) {
    PAs[A_Callback()] := 1;
  } else {
    x := x + 1;
  }
}

procedure {:atomic}{:layer 1}
{:IS "A_Service","INV"}{:elim "A_Callback"}
_Service() returns ({:pending_async "A_Callback"} PAs: [PA]int)
{
  PAs := MapConst(0);
  PAs[A_Callback()] := 1;
}
procedure {:yields}{:layer 0}{:refines "_Service"} Service ()
{
  async call Callback();
}

procedure {:both}{:layer 1} A_Callback ()
modifies x;
{ x := x + 1; }
procedure {:yields}{:layer 0}{:refines "A_Callback"} Callback ();
