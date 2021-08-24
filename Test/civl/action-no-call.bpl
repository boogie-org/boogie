// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:atomic}{:layer 2} foo () {}

type {:pending_async}{:datatype} PA;

procedure {:atomic}{:layer 2} atomic ()
{
  call foo();
}

procedure {:intro}{:layer 2} intro ()
{
  call foo();
}

procedure {:IS_invariant}{:layer 2} IS_invariant () returns ({:pending_async} PAs:[PA]int)
{
  call foo();
}
procedure {:IS_abstraction}{:layer 2} IS_abstraction ()
{
  call foo();
}
