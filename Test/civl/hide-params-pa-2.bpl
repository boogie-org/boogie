// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:pending_async}{:datatype} PA;
function {:constructor} A(i:int) : PA;

procedure {:atomic}{:layer 1,2} SPEC () returns ({:pending_async "A"} PAs:[PA]int)
{
  PAs := (lambda pa:PA :: 0)[A(1) := 1];
}

procedure {:yields}{:layer 1}{:refines "SPEC"} b ()
{
  async call a(true, 1, 2.3); // This call is already to action A when it is turned into a pending async.
}

procedure {:yields}{:layer 0}{:refines "SPEC"} c ()
{
  async call a(true, 1, 2.3); // This call is still to procedure a when it is turned into a pending async.
}

procedure {:atomic}{:layer 1,2} A (i:int) { }

procedure {:yields}{:layer 0}{:refines "A"} a ({:hide} b:bool, i:int, {:hide} r:real);
