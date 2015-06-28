// RUN: %boogie -printModel:2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure M (i: int) {
  assert i != 0;
}
