procedure {:yields} X();
ensures {:atomic 0} |{ A: return true; }|;

procedure {:yields} Y();
ensures {:left 0} |{ A: return true; }|;

procedure {:yields} main() {
  yield;
  call X();
  while (*)
//  invariant {:terminates} true;
  {
    call Y();
  }
  yield;
  assert {:phase 1} true;
}