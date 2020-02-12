// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure ReducingLambdaBodies() {
	var a, b: int;
	var f, g: [int]int;

	f := (lambda x: int :: a + b);
	g := (lambda x: int :: b + a);
	assert f == g; // should pass

	f := (lambda x: int :: x + a);
	g := (lambda x: int :: a + x);
	assert f == g; // should fail
}

procedure ReducingLambdaBodies2() {
	var a, b: int;
	var f, g: [int]int;
	var f2, g2: [int,int]int;

	f := (lambda x: int :: x + a);
	g := (lambda x: int :: a + x);
	assert f != g; // should fail
}

procedure ReducingLambdaBodies3() {
	var a, b: int;
	var f, g: [int,int]int;
	f := (lambda x, y: int :: x + y);
	g := (lambda x, y: int :: y + x);
	assert f == g; // should fail
}

procedure MultibleBoundVars() {
	var a, b: int;
	var f, g: [int,int,bool]bool;
	f := (lambda x: int, y: int, z: bool :: if y == (a - b)       then x + (a + b * a) > b else z == (a > b));
	g := (lambda x: int, y: int, z: bool :: if y == (b + a - 2*b) then x + (a * b + a) > b else z == (b < a));
	assert f == g; // should pass
}

function g(int,int) : int;

procedure Triggers'(w: int, w': int) {
	var a,b : [int]bool;
	a := (lambda x:int :: (forall u:int :: { g(u,w) } x == g(u,w)));
	b := (lambda y:int :: (forall v:int :: { g(v,w') } y == g(v,w')));
	assert w == w' ==> a == b;
	b := (lambda y:int :: (forall v:int :: y == g(v,w')));
	assert w == w' ==> a == b; // should fail because triggers are different
}
