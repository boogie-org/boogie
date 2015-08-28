// RUN: %boogie -z3multipleErrors -errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure Foo(x:int) 
{
  var ok:bool;
  
  ok := true;  

  if (x == 1) {
     ok := false;
  } else if (x == 2) {
     ok := false;
  } else if (x == 3) {
     ok := false;
  }
    
  assert ok;

}
