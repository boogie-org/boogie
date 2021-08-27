// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure {:yields}{:layer 1} Service ()
{
  async call Callback();
}

procedure {:yields}{:layer 0} Callback ();
