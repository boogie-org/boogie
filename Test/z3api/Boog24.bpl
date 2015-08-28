type ref;
 
function LIFT(a:bool) returns (int);
axiom(forall a:bool :: {LIFT(a)} a <==> LIFT(a) != 0);

procedure  main ( ) 

{
var a : int;
var b : int;
var c : int;

c := LIFT (b < a) ;
assert (c != 0 <==> b < a);

}

