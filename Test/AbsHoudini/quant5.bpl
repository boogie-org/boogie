function {:existential true} {:absdomain "Intervals"} b1(x: int) : bool;

procedure foo ()
{
  var arr: [int] int;
  assume (forall x: int :: arr[x] == 0);
  arr[5] := 1;

  assert (exists x: int :: arr[x] == 1 && b1(x));
}

