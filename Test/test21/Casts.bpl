

procedure P() returns () {
  var m : [int]int, n : [int]int, x : int;

  assume m[x] == x;
  assume n[x] == 1;

  assert n[m[x]] == 1;
  assert m[n[x]] == 1;    // should not be provable
}