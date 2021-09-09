// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:yields}{:layer 1} b ()
{
  call a(1);
}

procedure {:atomic}{:layer 1} A () { }

procedure {:yields}{:layer 0}{:refines "A"} a ({:hide} i:int);
