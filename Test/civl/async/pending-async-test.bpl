// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,3} x:int;

type {:pending_async}{:datatype} PA;
function {:constructor} A_Callback() : PA;

procedure {:yields}{:layer 2}{:refines "A_Callback"} Client ()
{
  call Service();
}

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
{:IS "A_Callback","INV"}{:elim "A_Callback"}
A_Service() returns ({:pending_async "A_Callback"} PAs: [PA]int)
{
  PAs := MapConst(0);
  PAs[A_Callback()] := 1;
}
procedure {:yields}{:layer 0}{:refines "A_Service"} Service ()
{
  async call Callback();
}

procedure {:both}{:layer 1,3} A_Callback ()
modifies x;
{ x := x + 1; }
procedure {:yields}{:layer 0}{:refines "A_Callback"} Callback ();
