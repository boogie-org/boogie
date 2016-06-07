var M: [int]int;

procedure {:inline 1} bar(y: int) returns (b: bool)
modifies M;
{
  if (b) {
    M[y] := M[y] + 1;
  } else {
    M[y] := M[y] - 1;
  }
}

procedure {:inline 1} foo(x: int, y: int) 
modifies M;
{
  var b: bool;

  call b := bar(y);
  if (b) {
    M[x] := M[x] + 1;
  } else {
    M[x] := M[x] - 1;
  }
}

procedure main(x: int, y: int) returns (b: bool)
requires x != y;
requires M[x] == M[y];
ensures !b ==> M[x] == M[y]+1;
ensures b ==> M[x]+1 == M[y];
modifies M;
{
  call foo(x, y);
  assert M[x] == M[y];
  call b := bar(y);
}
