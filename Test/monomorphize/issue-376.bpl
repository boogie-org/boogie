// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:datatype} Box _;
type {:datatype} Mut _;
type {:datatype} Pair _ _;

function {:constructor} Box<T>(x: T): Box T;
function {:constructor} Mut<T>(x: T): Mut T;
function {:constructor} Pair<T,U>(x: T, y: U): Pair T U;

procedure foo(b: Box (Box int)) returns (y: Mut (Box (Box int))) {
   y := Mut(b);
}

procedure bar(a: int, b: int) returns (y: Pair (Mut (Box int)) (Box (Mut int))) {
    y := Pair(Mut(Box(a)), Box(Mut(b)));
}
