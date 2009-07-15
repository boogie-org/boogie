
var fooVar: int;

procedure foo() 
modifies fooVar;
{
  fooVar:=5; 
  assert(fooVar==4);
  assert(fooVar==3);
}

// expected outcome: Errors
// expected assigment: []