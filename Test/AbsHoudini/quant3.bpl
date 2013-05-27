function {:existential true} {:absdomain "Intervals"} b1(x: int) : bool;

procedure foo ()
{
  assert (exists x: int :: (0 <= x && x <= 2) && b1(x));
}

