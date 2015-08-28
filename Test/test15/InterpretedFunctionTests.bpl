// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure addition(x: int, y: int) {
  assume x == 1;
  assume y == 2;
  assert x + y == 4;
}

procedure subtraction(x: int, y: int) {
  assume x == 1;
  assume y == 2;
  assert x - y == 4; //only shows x-y == -1 when run with /method:subtraction, WHY???
}

procedure multiplication(x: int, y: int) {
  assume x == 1;
  assume y == 2;
  assert x * y == 4;
}
