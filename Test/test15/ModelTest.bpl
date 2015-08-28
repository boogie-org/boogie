// RUN: %boogie -printModel:2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure M (s : ref, r : ref) {
  var  i : int, j : int;
  i := 0 + 1;
  j := i + 1;
  j := j + 1;
  j := j + 1;
  assert i == j;
  assert s == r;
}
type ref;
