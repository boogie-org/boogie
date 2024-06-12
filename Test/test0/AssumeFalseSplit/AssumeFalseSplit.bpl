// RUN: %parallel-boogie /vcsDumpSplits "%s" > "%t"
// RUN: mv %/S/Foo.split*.bpl %/S/Output/
// RUN: mv %/S/Foo.split*.dot %/S/Output/
// RUN: %diff "%s.expect" "%t"
// RUN: %diff %S/Foo.split.0.bpl.expect ./Output/Foo.split.0.bpl
// RUN: %diff %S/Foo.split.1.bpl.expect ./Output/Foo.split.1.bpl
// RUN: %diff %S/Foo.split.2.bpl.expect ./Output/Foo.split.2.bpl

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
