// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:builtin "Seq"} Seq _;
function {:builtin "seq.empty"} Seq_Empty_int(): Seq int;
function {:builtin "seq.len"} Seq_Len_int(a: Seq int): int;
function {:builtin "seq.++"} Seq_Concat_int(a: Seq int, b: Seq int): Seq int;
function {:builtin "seq.unit"} Seq_Unit_int(v: int): Seq int;
function {:builtin "seq.nth"} Seq_Nth_int(a: Seq int, i: int): int;
function {:builtin "seq.extract"} Seq_Extract_int(a: Seq int, pos: int, length: int): Seq int;

procedure test()
{
  var s: Seq int;

  s := Seq_Concat_int(Seq_Empty_int(), Seq_Unit_int(0));
  s := Seq_Concat_int(s, Seq_Unit_int(1));
  s := Seq_Concat_int(s, Seq_Unit_int(2));
  assert Seq_Len_int(s) == 3;
  assert Seq_Extract_int(s, 1, 2) == Seq_Concat_int(Seq_Unit_int(1), Seq_Unit_int(2));
  assert Seq_Nth_int(s, 1) == 1;
}
