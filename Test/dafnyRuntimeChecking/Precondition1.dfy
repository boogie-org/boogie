method foo(x: int, y: int)
  requires 0 <= x;
  requires y <= 0;
{}

method Main()
{
  foo(2, -7);
}
