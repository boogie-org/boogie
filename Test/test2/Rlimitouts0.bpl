// RUN: %boogie -rlimit:100 "%s" | %OutputCheck "%s"

procedure TestRlimit0(in: [int]int, len: int) returns (out: [int]int);
  requires in[0] == 0 && (forall i: int :: 0 <= i ==> in[i + 1] == in[i] + 1);
  requires 0 < len;
  ensures (forall j: int :: 0 <= j && j < len ==> out[j] == in[j]);

implementation TestRlimit0(in: [int]int, len: int) returns (out: [int]int)
{
    // CHECK-L: ${CHECKFILE_NAME}(${LINE:-2},16): Verification out of resource (TestRlimit0)
    var i : int;

    i := 0;
    out[i] := 0;
    while (i < len)
      invariant 0 <= i && i <= len;
      invariant out[0] == 0 && (forall j: int :: 0 <= j && j < i ==> out[j] == in[j]);
    {
        out[i] := in[i];
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

procedure TestRlimit1(in: [int]int, len: int) returns (out: [int]int);
  requires in[0] == 0 && (forall i: int :: 0 <= i ==> in[i + 1] == in[i] + 1);
  requires 0 < len;
  ensures (forall j: int :: 0 <= j && j < len ==> out[j] == in[j]);

implementation {:rlimit 60000} TestRlimit1(in: [int]int, len: int) returns (out: [int]int)
{
    var i : int;

    i := 0;
    out[i] := 0;
    while (i < len)
      invariant 0 <= i && i <= len;
      invariant out[0] == 0 && (forall j: int :: 0 <= j && j < i ==> out[j] == in[j]);
    {
        out[i] := in[i];
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

procedure TestRlimit2(in: [int]int, len: int) returns (out: [int]int);
  requires in[0] == 0 && (forall i: int :: 0 <= i ==> in[i + 1] == in[i] + 1);
  requires 0 < len;
  ensures (forall j: int :: 0 <= j && j < len ==> out[j] == in[j]);

implementation {:rlimit 200} TestRlimit2(in: [int]int, len: int) returns (out: [int]int)
{
    // CHECK-L: ${CHECKFILE_NAME}(${LINE:-2},30): Verification out of resource (TestRlimit2)
    var i : int;

    i := 0;
    out[i] := 0;
    while (i < len)
      invariant 0 <= i && i <= len;
      invariant out[0] == 0 && (forall j: int :: 0 <= j && j < i ==> out[j] == in[j]);
    {
        out[i] := in[i];
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
// CHECK-L: Boogie program verifier finished with 1 verified, 0 errors, 2 out of resource
