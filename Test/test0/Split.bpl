// RUN: %parallel-boogie /vcsDumpSplits "%s" > "%t"
// RUN: mv %/S/Ex.split* %/S/Output/
// RUN: %diff "%s.expect" "%t"
// RUN: %diff ./Output/Ex.split.0.bpl ./Output/Ex.split.0.bpl
// RUN: %diff ./Output/Ex.split.1.bpl ./Output/Ex.split.1.bpl
// RUN: %diff ./Output/Ex.split.2.bpl ./Output/Ex.split.2.bpl
// RUN: %diff ./Output/Ex.split.3.bpl ./Output/Ex.split.3.bpl

procedure Ex() returns (y: int)
  ensures y >= 0;
{
  var x: int;
  x := 5;
  y := 0;
  while (x > 0)
    invariant x + y == 5;
    invariant x*x <= 25;
  {
    x := x - 1;
    assert {:split_here} (x+y) * (x+y) > 25;
    y := y + 1;
    if (x < 3) {
      assert 2 < 2;
      assert {:split_here} y*y > 4;
    }
    else {
      assert {:split_here} y*y*y < 8;
      assert 2 < 2;
    }
    assert {:split_here} (x+y) * (x+y) == 25;
  }
}
