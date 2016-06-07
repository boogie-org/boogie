// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Test the implementation of free calls. These calls don't check the preconditions of the
// called procedure in the caller.


procedure Uncallable(i: int)
  requires 0 <= i;
  free requires true;
  requires false;
{

}

procedure UncallableReturn(i: int) returns (b: bool)
  requires 0 <= i;
  free requires true;
  requires false;
{
    b := true;
}

function T(b: bool) : bool
{
    b == true
}

procedure TestCallForall(b: bool)
  requires T(b);
  free requires true;
  ensures T(b);
{

}


procedure NormalCall0()
{
    call Uncallable(0); // error: precondition violation
}

procedure NormalCall1()
{
    call Uncallable(-1); // error: precondition violation
}

procedure FreeCall0()
{
    free call Uncallable(0);
}

procedure FreeCall1()
{
    free call Uncallable(-1);
}

procedure NormalCall2()
{
    var b: bool;

    call b := UncallableReturn(0); // error: precondition violation
}

procedure NormalCall3()
{
    var b: bool;

    call b := UncallableReturn(-1); // error: precondition violation
}

procedure FreeCall3()
{
    var b: bool;

    free call b := UncallableReturn(0);
}

procedure FreeCall4()
{
    var b: bool;

    free call b := UncallableReturn(-1);
}

