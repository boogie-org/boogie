type ref;
function AtLeast(int, int) returns ([int]bool);
axiom(forall n:int, x:int :: {AtLeast(n,x)} AtLeast(n,x)[x]);

var myInt:int;
procedure  main() 
modifies myInt;
ensures myInt==5;
{
  myInt:=4;
}