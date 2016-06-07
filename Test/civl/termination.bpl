// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure {:yields} {:layer 0} X();
ensures {:atomic} |{ A: return true; }|;

procedure {:yields} {:layer 0} Y();
ensures {:left} |{ A: return true; }|;

procedure {:yields} {:layer 1} main() {
  yield;
  call X();
  while (*)
  {
    call Y();
  }
  yield;
  assert {:layer 1} true;
}
