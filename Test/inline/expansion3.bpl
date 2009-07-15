function foo3(x:int, y:bool) returns(bool);
axiom {:inline true} (forall y:bool, x:int :: foo3(x,y) == foo3(x,y));

axiom foo3(1,false);

procedure baz1()
  requires foo3(2,false);
{
  assume foo3(1,true);
}

function x1(x:int) returns(bool);
axiom {:inline true} (forall x:int :: x1(x) <==> x > 0);
axiom {:inline true} (forall x:int :: x1(x) <==> x >= 1);

procedure bar()
{
  assert x1(3);
}
