// RUN: %boogie -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:pending_async}{:datatype} PA;
function {:pending_async "A"}{:constructor} A_PA() : PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 1,2} A () {}

procedure {:left}{:layer 1} B () returns ({:pending_async "A"} PAs:[PA]int)
{
  PAs := NoPAs()[A_PA() := 1];
}

procedure {:left}{:layer 1} C (flag:bool) returns ({:pending_async "A"} PAs:[PA]int)
{
  PAs := NoPAs();
  if (flag) {
    PAs := PAs[A_PA() := 1];
  }
}

procedure {:yields}{:layer 0}{:refines "B"} b ();
procedure {:yields}{:layer 0}{:refines "C"} c (flag:bool);


////////////////////////////////////////////////////////////////////////////////

// Verifies
procedure {:yields}{:layer 1}{:refines "TEST1"} test1 ()
{
  yield;
  call b();
  call b();
  yield;
}

procedure {:atomic}{:layer 2} TEST1 () returns ({:pending_async "A"} PAs:[PA]int)
{
  PAs := NoPAs()[A_PA() := 2];
}

////////////////////////////////////////////////////////////////////////////////

// Fails
procedure {:yields}{:layer 1}{:refines "TEST2"} test2 ()
{
  yield;
  call b();
  call b();
  yield;
}

procedure {:atomic}{:layer 2} TEST2 () returns ({:pending_async "A"} PAs:[PA]int)
{
  PAs := NoPAs()[A_PA() := 1];
}

////////////////////////////////////////////////////////////////////////////////

// Fails
procedure {:yields}{:layer 1}{:refines "TEST3"} test3 ()
{
  yield;
  call c(true);
  yield;
}

procedure {:atomic}{:layer 2} TEST3 () returns () {}

////////////////////////////////////////////////////////////////////////////////

// Verifies
procedure {:yields}{:layer 1}{:refines "TEST4"} test4 ()
{
  yield;
  call c(false);
  yield;
}

procedure {:atomic}{:layer 2} TEST4 () returns () {}

////////////////////////////////////////////////////////////////////////////////

// Verifies
procedure {:yields}{:layer 1}{:refines "TEST5"} test5 ()
{
  var i:int;
  var {:pending_async}{:layer 1} PAs:[PA]int;
  yield;
  i := 0;
  while (i < 10)
  invariant {:layer 1}{:terminates} true;
  invariant {:layer 1} 0 <= i && i <= 10;
  invariant {:layer 1} PAs == NoPAs()[A_PA() := i];
  {
    call b();
    i := i + 1;
  }
  yield;
}

procedure {:atomic}{:layer 2} TEST5 () returns ({:pending_async "A"} PAs:[PA]int)
{
  PAs := NoPAs()[A_PA() := 10];
}
