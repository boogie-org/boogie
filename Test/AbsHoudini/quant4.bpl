function {:existential true} {:absdomain "IA[HoudiniConst]"} b1() : bool;

procedure foo ()
{
  assert (exists x: int :: (0 <= x && x <= 2) && b1());
}

