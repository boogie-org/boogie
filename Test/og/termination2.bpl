// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure {:yields} {:phase 0} X();
ensures {:atomic} |{ A: return true; }|;

procedure {:yields} {:phase 0} Y();
ensures {:left} |{ A: return true; }|;

procedure {:yields} {:phase 1} main() {
  yield;
  call X();
  while (*)
  invariant {:terminates} {:phase 1} true;
  {
    call Y();
  }
  yield;
  assert {:phase 1} true;
}
