// RUN: %parallel-boogie -normalizeNames:1 -printModel:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure M (s: ref) {
  assert s != null;
}
type ref;
const null: ref;
