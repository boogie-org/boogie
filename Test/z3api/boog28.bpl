type ref;
 
function LIFT(x:bool) returns (int);
axiom(forall x:bool :: {LIFT(x)} x <==> LIFT(x) != 0);

procedure  main ( ) 

{
var a : int;
var b : int;
var c : int;

c := LIFT (b == a) ;
assert (c != 0 <==> b == a);

}

