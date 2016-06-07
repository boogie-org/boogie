type ref;
function choose(a:bool, b:int, c:int) returns (x:int);
axiom(forall a:bool, b:int, c:int :: {choose(a,b,c)} a ==> choose(a,b,c) == b);


var myInt:int;
procedure  main() 
modifies myInt;
ensures myInt==5;
{
  myInt:=4;
}