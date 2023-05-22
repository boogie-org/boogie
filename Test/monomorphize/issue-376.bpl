// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Box<T> { Box(x: T) }
datatype Mut<T> { Mut(x: T) }
datatype Pair<T, U> { Pair(x: T, y: U) }

procedure foo(b: Box (Box int)) returns (y: Mut (Box (Box int))) {
   y := Mut(b);
}

procedure bar(a: int, b: int) returns (y: Pair (Mut (Box int)) (Box (Mut int))) {
    y := Pair(Mut(Box(a)), Box(Mut(b)));
}
