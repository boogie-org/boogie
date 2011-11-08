function {:inline true} xxgz(x:int) returns(bool)
 { x > 0 }
function {:inline true} xxf1(x:int,y:bool) returns(int)
  { x + 1 }

axiom (forall z:int :: z>12 ==> xxgz(z));
axiom (forall y:int, x:bool :: xxf1(y, x) > 1 ==> y > 0);

procedure foo()
{
  assert xxgz(12);
  assert xxf1(3,true) == 4;
}

