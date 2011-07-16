var x: bv32;

procedure main() 
modifies x;
{

  x := 0bv32;
  assert 1bv32 != 0bv32;
  /*
  assume x == 1bv32;
  assert x == 0bv32;
  assert x == 1bv32 && x == 0bv32;
  assert 1bv32 == 0bv32;
  assert false;*/
}
