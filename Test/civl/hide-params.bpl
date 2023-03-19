// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 1} b ()
{
  call a(1);
}

action {:layer 1} A () { }

yield procedure {:layer 0} a ({:hide} i:int) refines A;
