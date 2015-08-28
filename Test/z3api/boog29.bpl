type ref;

function LIFT(x:bool) returns (int);
axiom(forall x:bool :: {LIFT(x)} x <==> LIFT(x) != 0);

procedure  main ( ) 

{
var c: int;
c := LIFT(false);
assert (c==0);

c := LIFT(true);
assert (c!=0);
/*
c := LIFT(1==5);
assert (c==0);
*/
}

