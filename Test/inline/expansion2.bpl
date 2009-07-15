function xxgz(x:int) returns(bool);
function xxf1(x:int,y:bool) returns(int);
axiom {:inline true} (forall x:int :: xxgz(x) <==> x > 0);
axiom {:inline true} (forall x:int, y:bool :: xxf1(x,y) == x+1);

axiom (forall z:int :: z>12 ==> xxgz(z));
axiom (forall y:int, x:bool :: xxf1(y, x) > 1 ==> y > 0);

procedure foo()
{
  assert xxgz(12);
  assert xxf1(3,true) == 4;
}

