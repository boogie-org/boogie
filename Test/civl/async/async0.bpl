// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
yield procedure {:layer 1} Service ()
{
  async call Callback();
}

yield procedure {:layer 0} Callback ();
