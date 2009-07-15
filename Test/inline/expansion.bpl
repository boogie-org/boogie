const q : int;
const p : bool;
function foo(x:int, y:bool) returns(bool);
function foo1(x:int, y:bool) returns(bool);
function foo2(x:int, y:bool) returns(bool);
function foo3(x:int, y:bool) returns(bool);
// OK
axiom {:inline false} (forall x:int, y:bool :: foo(x,p) <==> x > 10 && y);
axiom {:inline true} (forall x:int, y:bool :: foo1(x,y) == (x > 10 && y));
axiom {:inline true} (forall x:int, y:bool :: foo2(x,y) == (q > 10 && y));
axiom {:inline true} (forall y:bool, x:int :: foo3(x,y) == foo3(x,y));
// fail
axiom {:inline 1} (forall x:int, y:bool :: foo(x,y) <==> x > 10 && y);
axiom {:inline true} (forall x:int, y:bool :: foo(x,p) <==> x > 10 && y);
axiom {:inline true} (forall y:bool :: foo(q,y) == (q > 10 && y));
axiom {:inline true} (forall x:int, y:bool, z:int :: foo(x,y) == (q > 10 && y));
axiom {:inline true} (forall y:bool, x:int :: foo3(x,y) == (q > 10 && y));
axiom {:inline true} true;
axiom {:inline true} (forall y:bool, x:int :: foo3(x,true) == (q > 10 && y));


procedure baz1()
{
  assert foo3(1,true);
}

procedure baz2()
{
  assert foo1(true,true);
}

function foo4(x:int, y:int) returns(bool);
axiom {:inline true} (forall x:int,z:int :: foo4(x,x) == (x > 0));
