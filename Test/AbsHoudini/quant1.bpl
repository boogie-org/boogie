function {:existential true} {:absdomain "IA[Intervals]"} b1(x: int) : bool;

procedure foo ()
{
  assert (forall x: int :: (0 <= x && x <= 2) ==> b1(x));
}

