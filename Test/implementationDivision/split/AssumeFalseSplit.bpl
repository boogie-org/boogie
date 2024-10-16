// RUN: %boogie /printSplit:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure Foo()
{
  if (*) { 
    assert 2 == 1 + 1; 
    assume false; 
  } 
  assume 2 == 1 + 1; 
  assert {:split_here} 2 == 2;
  assert {:split_here} 3 == 2 + 1;
  assert 1 == 1;
}
