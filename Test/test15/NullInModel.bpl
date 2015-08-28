// RUN: %boogie -printModel:2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure M (s: ref) {
  assert s != null;
}
type ref;
const null: ref;
