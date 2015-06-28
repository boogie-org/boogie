// RUN: %boogie -stratifiedInline:1 -vc:i "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var M: [int]int;

procedure bar(y: int) returns (b: bool)
modifies M;
{
  if (b) {
    M[y] := M[y] + 1;
  } else {
    M[y] := M[y] - 1;
  }
}

procedure foo(x: int, y: int) 
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

procedure {:entrypoint} main(x: int, y: int) returns (b: bool)
modifies M;
{
  assume x != y;
  assume M[x] == M[y];
  call foo(x, y);
  if (M[x] == M[y]) {
    call b := bar(y);
    assume (if b then M[x]+1 != M[y] else M[x] != M[y]+1);
  }
}
