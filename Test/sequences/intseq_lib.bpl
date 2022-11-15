// RUN: %parallel-boogie -lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure test()
{
  var s: Seq int;

  s := Seq_Concat(Seq_Empty(), Seq_Unit(0));
  s := Seq_Concat(s, Seq_Unit(1));
  s := Seq_Concat(s, Seq_Unit(2));
  assert Seq_Len(s) == 3;
  assert Seq_Extract(s, 1, 2) == Seq_Concat(Seq_Unit(1), Seq_Unit(2));
  assert Seq_Nth(s, 1) == 1;
}
