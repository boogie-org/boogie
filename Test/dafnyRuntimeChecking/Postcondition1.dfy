var x: int;
var y: int;

method Main()
  modifies this`x, this`y;
  ensures 0 <= x;
  ensures y <= 0;
{
  x := 2;
  y := -7;
}
