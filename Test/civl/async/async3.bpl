// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,3} x:int;

type {:pending_async}{:datatype} PA;
function {:constructor} A_Inc() : PA;

procedure {:yields}{:layer 2}{:refines "A_Inc"} Client ()
{
  call Service();
}

procedure {:IS_invariant}{:layer 1} INV() returns ({:pending_async "A_Inc"} PAs: [PA]int)
modifies x;
{
  if (*) {
    PAs[A_Inc()] := 1;
  } else {
    x := x + 1;
  	PAs := MapConst(0);
  }
}

procedure {:atomic}{:layer 1}
{:IS "A_Inc","INV"}{:elim "A_Inc"}
A_Service() returns ({:pending_async "A_Inc"} PAs: [PA]int)
{
  PAs[A_Inc()] := 1;
}
procedure {:yields}{:layer 0}{:refines "A_Service"} Service ()
{
  async call Callback();
}

procedure {:both}{:layer 1,3} A_Inc ()
modifies x;
{ x := x + 1; }
procedure {:yields}{:layer 0}{:refines "A_Inc"} Callback ();
