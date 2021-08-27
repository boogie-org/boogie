// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure {:atomic} {:layer 1} AtomicX() { }

procedure {:yields} {:layer 0} {:refines "AtomicX"} X();

procedure {:yields} {:layer 0} Y();

procedure {:yields} {:layer 1} main() {
  call X();
  while (*)
  {
    call Y();
  }
}
