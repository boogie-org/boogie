// RUN: %boogie -timeLimit:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure TestTimeouts0(in: [int]int, len: int) returns (out: [int]int)
  requires in[0] == 0 && (forall i: int :: 0 <= i ==> in[i + 1] == in[i] + 1);
  requires 0 < len;
  ensures (forall j: int :: 0 <= j && j < len ==> out[j] == j);
{
    var i : int;

    i := 0;
    out[i] := 0;
    while (i < len)
      invariant 0 <= i && i <= len;
      invariant out[0] == 0 && (forall j: int :: 0 <= j && j < i ==> out[j + 1] == out[j] + 1);
    {
        out[i + 1] := out[i] + 1;
        i := i + 1;
    }

    i := 0;
    while (i < len)
      invariant 0 <= i && i <= len;
      invariant (forall j: int :: 0 <= j && j < i ==> out[j] == in[j]);
    {
        i := i + 1;
    }
}


procedure TestTimeouts1(in: [int]int, len: int) returns (out: [int]int);
  requires in[0] == 0 && (forall i: int :: 0 <= i ==> in[i + 1] == in[i] + 1);
  requires 0 < len;
  ensures (forall j: int :: 0 <= j && j < len ==> out[j] == j);

implementation {:timeLimit 8} TestTimeouts1(in: [int]int, len: int) returns (out: [int]int)
{
    var i : int;

    i := 0;
    out[i] := 0;
    while (i < len)
      invariant 0 <= i && i <= len;
      invariant out[0] == 0 && (forall j: int :: 0 <= j && j < i ==> out[j + 1] == out[j] + 1);
    {
        out[i + 1] := out[i] + 1;
        i := i + 1;
    }

    i := 0;
    while (i < len)
      invariant 0 <= i && i <= len;
      invariant (forall j: int :: 0 <= j && j < i ==> out[j] == in[j]);
    {
        i := i + 1;
    }
}


procedure TestTimeouts2(in: [int]int, len: int) returns (out: [int]int);
  requires in[0] == 0 && (forall i: int :: 0 <= i ==> in[i + 1] == in[i] + 1);
  requires 0 < len;
  ensures (forall j: int :: 0 <= j && j < len ==> out[j] == j);

implementation {:timeLimit 2} TestTimeouts2(in: [int]int, len: int) returns (out: [int]int)
{
    var i : int;

    i := 0;
    out[i] := 0;
    while (i < len)
      invariant 0 <= i && i <= len;
      invariant out[0] == 0 && (forall j: int :: 0 <= j && j < i ==> out[j + 1] == out[j] + 1);
    {
        out[i + 1] := out[i] + 1;
        i := i + 1;
    }

    i := 0;
    while (i < len)
      invariant 0 <= i && i <= len;
      invariant (forall j: int :: 0 <= j && j < i ==> out[j] == in[j]);
    {
        i := i + 1;
    }
}
