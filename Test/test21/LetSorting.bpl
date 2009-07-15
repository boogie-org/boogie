

procedure Array0() returns (z: int)
  ensures z >= 5;
{
L0:
  goto L1, L2;
L1:
  z := 10;
L2:
  z := 20;
  return;
}


