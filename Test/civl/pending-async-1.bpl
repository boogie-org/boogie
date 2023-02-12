// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 1,2} {:pending_async} A () {}

procedure {:left}{:layer 1} {:creates "A"} B ()
{
  call create_async(A());
}

procedure {:left}{:layer 1} {:creates "A"} C (flag:bool)
{
  if (flag) {
    call create_async(A());
  }
}

procedure {:yields}{:layer 0}{:refines "B"} b ();
procedure {:yields}{:layer 0}{:refines "C"} c (flag:bool);


////////////////////////////////////////////////////////////////////////////////

// Verifies
procedure {:yields}{:layer 1}{:refines "TEST1"} test1 ()
{
  call b();
  call b();
}

procedure {:atomic}{:layer 2} {:creates "A"} TEST1 ()
{
  call create_multi_asyncs(MapConst(0)[A() := 2]);
}

////////////////////////////////////////////////////////////////////////////////

// Fails
procedure {:yields}{:layer 1}{:refines "TEST2"} test2 ()
{
  call b();
  call b();
}

procedure {:atomic}{:layer 2} {:creates "A"} TEST2 ()
{
  call create_async(A());
}

////////////////////////////////////////////////////////////////////////////////

// Fails
procedure {:yields}{:layer 1}{:refines "TEST3"} test3 ()
{
  call c(true);
}

procedure {:atomic}{:layer 2} TEST3 () returns () {}

////////////////////////////////////////////////////////////////////////////////

// Verifies
procedure {:yields}{:layer 1}{:refines "TEST4"} test4 ()
{
  call c(false);
}

procedure {:atomic}{:layer 2} TEST4 () returns () {}

////////////////////////////////////////////////////////////////////////////////

// Verifies
procedure {:yields}{:layer 1}{:refines "TEST5"} test5 ()
{
  var i:int;
  var {:pending_async}{:layer 1} PAs:[A]int;

  i := 0;
  while (i < 10)
  invariant {:layer 1}{:cooperates} true;
  invariant {:layer 1} 0 <= i && i <= 10;
  invariant {:layer 1} PAs == MapConst(0)[A() := i];
  {
    call b();
    i := i + 1;
  }
}

procedure {:atomic}{:layer 2} {:creates "A"} TEST5 ()
{
  call create_multi_asyncs(MapConst(0)[A() := 10]);
}
