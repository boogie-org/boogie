// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function f<T>(x: T) : int;

type Field _;
const f1: Field int;
const f2: Field bool;

procedure p() {
	var y: <A>[Field A]bool;
	var z: <A>[Field A]int;

	assume (forall <T1,T2> x: <A>[Field A]T1, y: <A>[Field A]T2 :: x != y ==> f(x) != f(y));
	assert f(y) != f(z);
}
